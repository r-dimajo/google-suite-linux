const {
  app,
  BrowserWindow,
  WebContentsView,
  Menu,
  Tray,
  nativeImage,
  shell,
  ipcMain,
  dialog,
  session,
  desktopCapturer,
  globalShortcut,
  Notification,
  clipboard,
  screen
} = require('electron');
const path = require('path');
const fs = require('fs');
const os = require('os');
const crypto = require('crypto');
const https = require('https');
const {
  APPS,
  byId,
  byHost,
  detectApp,
  isInternal,
  isTrustedOrigin,
  isSafeExternalUrl,
  unwrapGoogleUrl
} = require('./apps');

// Hand a URL to the OS only for safe schemes (http/https/mailto/tel).
// Prevents pages from launching local files (file://) or arbitrary protocol handlers.
function safeOpenExternal(url) {
  if (!isSafeExternalUrl(url)) {
    console.warn('[Google Suite] Blocked openExternal for unsafe URL:', String(url).slice(0, 200));
    return false;
  }
  shell.openExternal(url).catch((err) => console.warn('openExternal failed:', err));
  return true;
}

// Linux Wayland & hardware flags
app.commandLine.appendSwitch('disable-background-timer-throttling');
app.commandLine.appendSwitch('disable-renderer-backgrounding');
app.commandLine.appendSwitch('disable-backgrounding-occluded-windows');

if (process.platform === 'linux') {
  app.commandLine.appendSwitch('ozone-platform-hint', 'auto');

  // Fix rendering on hybrid GPU (AMD iGPU + NVIDIA dGPU) under Wayland:
  // prevent Chromium from falling back to the software renderer (SwiftShader)
  // and ensure GPU rasterization is active.
  app.commandLine.appendSwitch('ignore-gpu-blocklist');
  app.commandLine.appendSwitch('enable-gpu-rasterization');
  app.commandLine.appendSwitch('enable-zero-copy');
  app.commandLine.appendSwitch('use-gl', 'desktop');
  // Hardware video decoding on AMD (VAAPI)
  app.commandLine.appendSwitch('enable-features', 'VaapiVideoDecoder,VaapiVideoEncoder');

  // Enforce Adwaita GTK window decorations (buttons and frame) only when genuinely in GNOME mode
  const de = (
    process.env.XDG_CURRENT_DESKTOP ||
    process.env.DESKTOP_SESSION ||
    process.env.GDMSESSION ||
    ''
  ).toLowerCase();

  const isKde = de.includes('kde') || de.includes('plasma') || process.argv.includes('--kde');
  const isGnome = !isKde && (
    process.argv.includes('--gnome') ||
    Boolean(process.env.MUTTER_DEBUG_DUMMY_MODE_SPECS) ||
    de.includes('gnome') ||
    de.includes('unity') ||
    de.includes('pantheon')
  );

  if (isGnome && !process.env.GTK_THEME) {
    process.env.GTK_THEME = 'Adwaita:dark';
  }
}

// Default application and web services locale to English
app.commandLine.appendSwitch('lang', 'en-US');

// Allow running an isolated/new instance for testing without conflicting with a background app
const allowMultiple =
  process.argv.includes('--new-instance') ||
  process.argv.includes('--isolated') ||
  Boolean(process.env.GAPPS_ISOLATED);

if (!allowMultiple) {
  const gotLock = app.requestSingleInstanceLock();
  if (!gotLock) {
    console.log("\n[Google Suite] Un'altra istanza dell'app e' gia' in esecuzione sul sistema.");
    console.log("[Google Suite] Il comando e' stato inoltrato alla finestra esistente.");
    console.log("[Google Suite] Per eseguire un'istanza di test separata (es. dentro Mutter/GNOME):");
    console.log("               google-suite --new-instance\n");
    app.quit();
    process.exit(0);
  }

  // Preserve existing Google logins, cookies, tabs, and settings from ~/.config/gapps
  const appData = app.getPath('appData');
  const legacyDir = path.join(appData, 'gapps');
  if (fs.existsSync(legacyDir)) {
    app.setPath('userData', legacyDir);
  }
} else {
  const testUserData = path.join(os.tmpdir(), `gapps-session-${process.pid}`);
  app.setPath('userData', testUserData);
}

const TABBAR_HEIGHT = 36;
const VERTICAL_TABBAR_WIDTH = 210;
const CONFIG_DIR = path.join(app.getPath('userData'));
const STATE_FILE = path.join(CONFIG_DIR, 'state.json');
const SETTINGS_FILE = path.join(CONFIG_DIR, 'settings.json');
const ICON_PATH = path.join(__dirname, 'icons', 'icon.png');
const ICONS_DIR = path.join(__dirname, 'icons', 'apps');
const NEW_TAB_URL = 'file://' + path.join(__dirname, 'newtab', 'index.html');

let mainWindow = null;
let tabbarView = null;
let tray = null;
app.isQuitting = false;

let state = {
  tabs: [],
  active: null,
  split: {
    enabled: false,
    tabId: null,
    direction: 'horizontal', // 'horizontal' (side-by-side) | 'vertical' (stacked)
    ratio: 0.5 // primary pane width/height ratio (0.2 to 0.8)
  }
};

let settings = {
  open_at_startup: true,
  start_minimized: false,
  memory_saver: true,
  tab_layout: 'horizontal', // 'horizontal' | 'vertical'
  desktop_theme: 'auto', // 'auto' | 'gnome' | 'kde'
  close_action: 'tray', // 'tray' | 'quit'
  window_bounds: null
};

function isVerticalTabs() {
  return settings.tab_layout === 'vertical';
}

function getDesktopEnvironment() {
  if (process.env.MUTTER_DEBUG_DUMMY_MODE_SPECS) {
    return 'gnome';
  }

  const de = (
    process.env.XDG_CURRENT_DESKTOP ||
    process.env.DESKTOP_SESSION ||
    process.env.GDMSESSION ||
    ''
  ).toLowerCase();

  if (de.includes('kde') || de.includes('plasma')) {
    return 'kde';
  }
  if (de.includes('gnome') || de.includes('unity') || de.includes('pantheon')) {
    return 'gnome';
  }
  return 'kde';
}

let cliThemeOverride = null;
if (process.argv.includes('--gnome')) {
  cliThemeOverride = 'gnome';
} else if (process.argv.includes('--kde')) {
  cliThemeOverride = 'kde';
}

function getEffectiveTheme() {
  if (cliThemeOverride) return cliThemeOverride;
  if (settings.desktop_theme && settings.desktop_theme !== 'auto') {
    return settings.desktop_theme;
  }
  return getDesktopEnvironment();
}

function setDesktopTheme(theme) {
  settings.desktop_theme = theme;
  saveSettings();
  broadcastState();
}

// Map of tabId -> WebContentsView
const tabViews = new Map();

// Generate distinct, crisp 128x128 PNG icons for all Google apps from SVG vectors
async function ensureAppIcons() {
  if (app.isPackaged) return;
  try {
    fs.mkdirSync(ICONS_DIR, { recursive: true });
    const { ICONS } = require('./svg-icons');

    const metaPath = path.join(ICONS_DIR, '.meta.json');
    let meta = {};
    try {
      if (fs.existsSync(metaPath)) {
        meta = JSON.parse(fs.readFileSync(metaPath, 'utf8'));
      }
    } catch (_) {}

    const newMeta = { ...meta };
    const keysToGenerate = [];

    for (const [key, svg] of Object.entries(ICONS)) {
      if (['audio', 'muted', 'pin', 'newtab', 'lock', 'layoutVertical', 'layoutHorizontal'].includes(key)) continue;
      const pngPath = path.join(ICONS_DIR, `${key}.png`);
      const hash = crypto.createHash('md5').update(svg).digest('hex');
      if (!fs.existsSync(pngPath) || fs.statSync(pngPath).size <= 200 || meta[key] !== hash) {
        keysToGenerate.push({ key, hash });
      }
    }

    if (keysToGenerate.length === 0) return;

    // Use an offscreen BrowserWindow to render real SVG vectors into 128x128 PNGs
    const offscreenWin = new BrowserWindow({
      show: false,
      width: 128,
      height: 128,
      frame: false,
      transparent: true,
      webPreferences: {
        offscreen: true,
        contextIsolation: true
      }
    });

    for (const { key, hash } of keysToGenerate) {
      const svg = ICONS[key];
      if (!svg) continue;
      const pngPath = path.join(ICONS_DIR, `${key}.png`);

      const cleanSvg = svg
        .replace(/width="[^"]*"/, 'width="128"')
        .replace(/height="[^"]*"/, 'height="128"');

      const html = `<!DOCTYPE html><html><head><style>html,body{margin:0;padding:0;width:128px;height:128px;overflow:hidden;background:transparent;display:flex;align-items:center;justify-content:center;}</style></head><body>${cleanSvg}</body></html>`;

      try {
        await offscreenWin.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(html)}`);
        await new Promise((r) => setTimeout(r, 70));
        const image = await offscreenWin.webContents.capturePage();
        const pngBuffer = image.toPNG();
        if (pngBuffer && pngBuffer.length > 200) {
          fs.writeFileSync(pngPath, pngBuffer);
          newMeta[key] = hash;
        }
      } catch (e) {
        console.error(`Failed to rasterize SVG for ${key}:`, e);
      }
    }

    try {
      fs.writeFileSync(metaPath, JSON.stringify(newMeta, null, 2));
    } catch (_) {}

    try { offscreenWin.destroy(); } catch (_) {}
  } catch (err) {
    console.error('Failed to generate app PNG icons via offscreen window:', err);
  }
}

function getAppIconPath(appId, badged = false) {
  if (badged) {
    const badgedPath = path.join(ICONS_DIR, `${appId}_badged.png`);
    if (fs.existsSync(badgedPath) && fs.statSync(badgedPath).size > 200) {
      return badgedPath;
    }
  }
  const p = path.join(ICONS_DIR, `${appId}.png`);
  if (fs.existsSync(p) && fs.statSync(p).size > 200) {
    return p;
  }
  return ICON_PATH;
}

function getTrayIconPath() {
  const p = path.join(ICONS_DIR, 'tray.png');
  if (fs.existsSync(p) && fs.statSync(p).size > 200) {
    return p;
  }
  return ICON_PATH;
}

function getTrayBadgedIconPath() {
  const p = path.join(ICONS_DIR, 'tray_badged.png');
  if (fs.existsSync(p) && fs.statSync(p).size > 200) {
    return p;
  }
  return getTrayIconPath();
}

function ensureDesktopFile() {
  if (process.platform !== 'linux') return;
  // When installed as a system package (.deb, rpm, etc.), system desktop integration already exists
  if (app.isPackaged) return;

  try {
    const home = process.env.HOME || app.getPath('home');
    const appsDir = path.join(home, '.local', 'share', 'applications');
    const iconsDir = path.join(home, '.local', 'share', 'icons', 'hicolor', '128x128', 'apps');
    const targetIconPathSuite = path.join(iconsDir, 'google-suite.png');
    const sourceIcon = path.resolve(ICON_PATH);
    const launcherPath = path.join(__dirname, 'google-suite');

    // 1. Install hicolor icon for google-suite
    try {
      if (!fs.existsSync(iconsDir)) {
        fs.mkdirSync(iconsDir, { recursive: true });
      }
      fs.copyFileSync(sourceIcon, targetIconPathSuite);
    } catch (_) {}

    // 2. Install .desktop file for development mode
    if (!fs.existsSync(appsDir)) {
      fs.mkdirSync(appsDir, { recursive: true });
    }

    const desktopContent = `[Desktop Entry]
Type=Application
Version=1.0
Name=Google Suite
Comment=Google Workspace desktop client for Linux
Exec=${launcherPath}
Icon=${sourceIcon}
Terminal=false
StartupWMClass=google-suite
StartupNotify=true
Categories=Network;Office;Chat;
`;

    const suiteDesktop = path.join(appsDir, 'google-suite.desktop');
    fs.writeFileSync(suiteDesktop, desktopContent, 'utf8');

    // 3. Notify desktop environment
    try {
      const { exec } = require('child_process');
      exec('update-desktop-database ~/.local/share/applications/ 2>/dev/null; kbuildsycoca6 --noincremental 2>/dev/null || kbuildsycoca5 --noincremental 2>/dev/null');
    } catch (_) {}
  } catch (err) {
    console.warn('Could not ensure desktop integration:', err);
  }
}

function manageAutostart(enable) {
  if (process.platform !== 'linux') return;
  try {
    const home = process.env.HOME || app.getPath('home');
    const autostartDir = path.join(home, '.config', 'autostart');
    const autostartFile = path.join(autostartDir, 'google-suite.desktop');
    const legacyFile = path.join(autostartDir, 'gapps.desktop');

    if (enable) {
      if (!fs.existsSync(autostartDir)) {
        fs.mkdirSync(autostartDir, { recursive: true });
      }

      const execCmd = app.isPackaged
        ? (process.env.APPIMAGE || 'google-suite')
        : path.join(__dirname, 'google-suite');
      const iconCmd = app.isPackaged ? 'google-suite' : path.resolve(ICON_PATH);

      const desktopContent = `[Desktop Entry]
Type=Application
Version=1.0
Name=Google Suite
Comment=Google Workspace desktop client for Linux
Exec=${execCmd}
Icon=${iconCmd}
Terminal=false
StartupWMClass=google-suite
StartupNotify=false
Categories=Network;Office;Chat;
X-GNOME-Autostart-enabled=true
X-KDE-autostart-after=panel
X-KDE-autostart-phase=2
`;
      fs.writeFileSync(autostartFile, desktopContent, 'utf8');
      if (fs.existsSync(legacyFile)) {
        try { fs.unlinkSync(legacyFile); } catch (_) {}
      }
    } else {
      if (fs.existsSync(autostartFile)) {
        fs.unlinkSync(autostartFile);
      }
      if (fs.existsSync(legacyFile)) {
        try { fs.unlinkSync(legacyFile); } catch (_) {}
      }
    }
  } catch (err) {
    console.warn('Could not manage autostart entry:', err);
  }
}

function loadSettings() {
  try {
    if (fs.existsSync(SETTINGS_FILE)) {
      const data = JSON.parse(fs.readFileSync(SETTINGS_FILE, 'utf8'));
      settings = Object.assign(settings, data);
    }
  } catch (err) {
    console.error('Failed to load settings:', err);
  }
  manageAutostart(settings.open_at_startup !== false);
}

function saveSettings() {
  try {
    fs.mkdirSync(CONFIG_DIR, { recursive: true });
    fs.writeFileSync(SETTINGS_FILE, JSON.stringify(settings, null, 2), 'utf8');
  } catch (err) {
    console.error('Failed to save settings:', err);
  }
}

function loadState() {
  try {
    if (fs.existsSync(STATE_FILE)) {
      const data = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
      if (data && Array.isArray(data.tabs) && data.tabs.length > 0) {
        state.tabs = data.tabs.map((t) => ({
          ...t,
          customTitle: t.customTitle || null,
          pinned: Boolean(t.pinned),
          locked: t.locked !== undefined ? Boolean(t.locked) : ['gmail', 'chat', 'calendar'].includes(t.app),
          unreadCount: 0,
          isAudible: false,
          isMuted: false,
          lastAccessed: Date.now()
        }));
        state.active = data.active || data.tabs[0].id;
        if (data.split && typeof data.split === 'object') {
          const splitTabExists = state.tabs.some((t) => t.id === data.split.tabId);
          state.split = {
            enabled: Boolean(data.split.enabled && splitTabExists && data.split.tabId !== state.active),
            tabId: splitTabExists ? data.split.tabId : null,
            direction: data.split.direction === 'vertical' ? 'vertical' : 'horizontal',
            ratio: typeof data.split.ratio === 'number' ? Math.max(0.2, Math.min(0.8, data.split.ratio)) : 0.5
          };
        }
        return;
      }
    }
  } catch (err) {
    console.error('Failed to load state:', err);
  }

  // Default initial tab: Gmail
  const defaultApp = byId('gmail') || APPS[0];
  const id = 'tab_' + Date.now();
  state.tabs = [
    {
      id,
      app: defaultApp.id,
      title: defaultApp.title,
      url: defaultApp.url,
      pinned: false,
      locked: true,
      unreadCount: 0,
      isAudible: false,
      isMuted: false,
      lastAccessed: Date.now()
    }
  ];
  state.active = id;
}

function saveStateSync() {
  try {
    fs.mkdirSync(CONFIG_DIR, { recursive: true });
    // Always sync current live webContents URLs if available before writing
    state.tabs.forEach((t) => {
      if (tabViews.has(t.id)) {
        try {
          const liveUrl = tabViews.get(t.id).webContents.getURL();
          if (liveUrl && !liveUrl.startsWith('file://') && liveUrl !== 'about:blank') {
            t.url = liveUrl;
          }
        } catch (_) {}
      }
    });
    fs.writeFileSync(
      STATE_FILE,
      JSON.stringify(
        {
          tabs: state.tabs.map((t) => ({
            id: t.id,
            app: t.app,
            title: t.title,
            customTitle: t.customTitle || null,
            url: t.url,
            pinned: Boolean(t.pinned),
            locked: Boolean(t.locked)
          })),
          active: state.active,
          split: state.split
        },
        null,
        2
      ),
      'utf8'
    );
  } catch (err) {
    console.error('Failed to save state:', err);
  }
}

let saveStateTimer = null;
function saveState() {
  clearTimeout(saveStateTimer);
  saveStateTimer = setTimeout(() => {
    saveStateSync();
  }, 300);
}

function broadcastState() {
  if (tabbarView && !tabbarView.webContents.isDestroyed()) {
    tabbarView.webContents.send('state-update', {
      tabs: state.tabs.map((t) => ({
        id: t.id,
        app: t.app,
        title: t.customTitle || t.title,
        customTitle: t.customTitle || null,
        url: t.url,
        pinned: Boolean(t.pinned),
        locked: Boolean(t.locked),
        unreadCount: t.unreadCount || 0,
        hasNotification: Boolean(t.hasNotification),
        isAudible: Boolean(t.isAudible),
        isMuted: Boolean(t.isMuted)
      })),
      active: state.active,
      split: state.split,
      apps: APPS,
      layout: settings.tab_layout || 'horizontal',
      theme: getEffectiveTheme()
    });
  }
}

function updateAppBadge() {
  const totalUnread = state.tabs.reduce((sum, t) => {
    const unread = Math.max(t.unreadCount || 0, t.hasNotification ? 1 : 0);
    return sum + unread;
  }, 0);
  if (app.setBadgeCount) {
    app.setBadgeCount(totalUnread);
  }
  if (tray) {
    tray.setToolTip(totalUnread > 0 ? `Google Suite (${totalUnread} unread)` : 'Google Suite');
    const trayIconPath = totalUnread > 0 ? getTrayBadgedIconPath() : getTrayIconPath();
    try {
      tray.setImage(nativeImage.createFromPath(trayIconPath));
    } catch (_) {}
  }
}

function isTabActivelyViewed(tabId) {
  if (!tabId) return false;
  const isCurrentActive = state.active === tabId;
  const isSplitSecondary = Boolean(state.split && state.split.enabled && state.split.tabId === tabId);
  if (!isCurrentActive && !isSplitSecondary) return false;

  const isWindowActive =
    mainWindow &&
    !mainWindow.isDestroyed() &&
    mainWindow.isVisible() &&
    !mainWindow.isMinimized() &&
    mainWindow.isFocused();

  return Boolean(isWindowActive);
}

// Whether a tab is on screen (active or split secondary, window shown and not minimized).
// Sent to tab-preload.js to drive document.hidden / visibilityState.
function computeTabVisible(tabId) {
  if (!tabId) return false;
  const shown =
    state.active === tabId ||
    Boolean(state.split && state.split.enabled && state.split.tabId === tabId);
  return Boolean(
    shown &&
      mainWindow &&
      !mainWindow.isDestroyed() &&
      mainWindow.isVisible() &&
      !mainWindow.isMinimized()
  );
}

const lastSentVisibility = new Map();

function sendTabVisibility(tabId, force = false) {
  const view = tabViews.get(tabId);
  if (!view || view.webContents.isDestroyed()) {
    lastSentVisibility.delete(tabId);
    return;
  }
  const visible = computeTabVisible(tabId);
  if (!force && lastSentVisibility.get(tabId) === visible) return;
  lastSentVisibility.set(tabId, visible);
  try {
    view.webContents.send('gapps-visibility', visible);
  } catch (_) {}
}

function syncTabVisibility() {
  for (const tabId of tabViews.keys()) {
    sendTabVisibility(tabId);
  }
  for (const tabId of Array.from(lastSentVisibility.keys())) {
    if (!tabViews.has(tabId)) lastSentVisibility.delete(tabId);
  }

  // The user is looking at the tab: drop the generic "new notification" dot.
  // Real unread counts stay until the web app reports them as read.
  let changed = false;
  state.tabs.forEach((t) => {
    if (t.hasNotification && isTabActivelyViewed(t.id)) {
      t.hasNotification = false;
      changed = true;
    }
  });
  if (changed) {
    updateAppBadge();
    broadcastState();
  }
}

function clearTabNotification(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;
  if (tab.hasNotification || (tab.unreadCount && tab.unreadCount > 0)) {
    tab.hasNotification = false;
    tab.unreadCount = 0;
    updateAppBadge();
    broadcastState();
  }
}

function updateBounds() {
  if (!mainWindow || mainWindow.isDestroyed()) return;
  const [width, height] = mainWindow.getContentSize();
  if (width <= 0 || height <= 0) return;

  const vertical = isVerticalTabs();

  if (tabbarView) {
    if (vertical) {
      tabbarView.setBounds({ x: 0, y: 0, width: VERTICAL_TABBAR_WIDTH, height });
    } else {
      tabbarView.setBounds({ x: 0, y: 0, width, height: TABBAR_HEIGHT });
    }
    try {
      if (tabbarView.webContents && !tabbarView.webContents.isDestroyed()) {
        tabbarView.webContents.invalidate();
      }
    } catch (_) {}
  }

  // Work area coordinates for web contents
  const contentX = vertical ? VERTICAL_TABBAR_WIDTH : 0;
  const contentY = vertical ? 0 : TABBAR_HEIGHT;
  const contentWidth = Math.max(0, vertical ? width - VERTICAL_TABBAR_WIDTH : width);
  const contentHeight = Math.max(0, vertical ? height : height - TABBAR_HEIGHT);

  const isSplitActive = Boolean(
    state.split &&
    state.split.enabled &&
    state.split.tabId &&
    state.split.tabId !== state.active &&
    tabViews.has(state.split.tabId)
  );

  const primaryView = state.active && tabViews.has(state.active) ? tabViews.get(state.active) : null;
  const secondaryView = isSplitActive ? tabViews.get(state.split.tabId) : null;

  if (primaryView && !secondaryView) {
    primaryView.setBounds({
      x: contentX,
      y: contentY,
      width: contentWidth,
      height: contentHeight
    });
    try {
      primaryView.setVisible(true);
      if (primaryView.webContents && !primaryView.webContents.isDestroyed()) {
        primaryView.webContents.invalidate();
      }
    } catch (_) {}
  } else if (primaryView && secondaryView) {
    const ratio = (state.split && state.split.ratio) || 0.5;
    const isHorizontalSplit = !state.split || state.split.direction !== 'vertical'; // default side-by-side

    if (isHorizontalSplit) {
      // Side-by-side (left / right)
      const dividerW = 4;
      const availableW = Math.max(0, contentWidth - dividerW);
      const w1 = Math.round(availableW * ratio);
      const w2 = availableW - w1;

      primaryView.setBounds({
        x: contentX,
        y: contentY,
        width: w1,
        height: contentHeight
      });
      secondaryView.setBounds({
        x: contentX + w1 + dividerW,
        y: contentY,
        width: w2,
        height: contentHeight
      });
    } else {
      // Stacked (top / bottom)
      const dividerH = 4;
      const availableH = Math.max(0, contentHeight - dividerH);
      const h1 = Math.round(availableH * ratio);
      const h2 = availableH - h1;

      primaryView.setBounds({
        x: contentX,
        y: contentY,
        width: contentWidth,
        height: h1
      });
      secondaryView.setBounds({
        x: contentX,
        y: contentY + h1 + dividerH,
        width: contentWidth,
        height: h2
      });
    }

    try {
      primaryView.setVisible(true);
      if (primaryView.webContents && !primaryView.webContents.isDestroyed()) {
        primaryView.webContents.invalidate();
      }
    } catch (_) {}
    try {
      secondaryView.setVisible(true);
      if (secondaryView.webContents && !secondaryView.webContents.isDestroyed()) {
        secondaryView.webContents.invalidate();
      }
    } catch (_) {}
  }
}

let resizeDebounceTimer = null;
function scheduleUpdateBounds() {
  updateBounds();
  if (resizeDebounceTimer) clearTimeout(resizeDebounceTimer);
  resizeDebounceTimer = setTimeout(() => {
    updateBounds();
    setTimeout(updateBounds, 120);
  }, 40);
}

const ALLOWED_PERMISSIONS = new Set([
  'notifications',
  'media',
  'display-capture',
  'mediaKeySystem',
  'clipboard-read',
  'clipboard-sanitized-write',
  'fullscreen',
  'pointerLock',
  'keyboardLock',
  'speaker-selection',
  'window-management',
  'screen-wake-lock'
]);

function isPermissionAllowed(permission, origin) {
  return ALLOWED_PERMISSIONS.has(permission) && isTrustedOrigin(origin);
}

function isWaylandSession() {
  return (
    (process.env.XDG_SESSION_TYPE || '').toLowerCase() === 'wayland' ||
    Boolean(process.env.WAYLAND_DISPLAY)
  );
}

// Ask the user which screen/window to share instead of silently picking the first one
function pickDisplaySource(sources) {
  if (!Array.isArray(sources) || sources.length === 0) return Promise.resolve(null);
  // On Wayland, getSources() goes through the xdg-desktop-portal dialog: the single
  // returned source is the one the user just picked there.
  if (sources.length === 1 && isWaylandSession()) return Promise.resolve(sources[0]);

  return new Promise((resolve) => {
    let done = false;
    const finish = (value) => {
      if (done) return;
      done = true;
      resolve(value);
    };

    const screens = sources.filter((src) => src.id.startsWith('screen:'));
    const windows = sources.filter((src) => !src.id.startsWith('screen:')).slice(0, 25);
    const items = [{ label: 'Condividi schermo', enabled: false }];
    screens.forEach((src, i) => {
      items.push({ label: `Schermo: ${src.name || i + 1}`, click: () => finish(src) });
    });
    if (windows.length > 0) {
      items.push({ type: 'separator' });
      windows.forEach((src) => {
        items.push({ label: `Finestra: ${(src.name || 'Senza titolo').slice(0, 80)}`, click: () => finish(src) });
      });
    }
    items.push({ type: 'separator' });
    items.push({ label: 'Annulla', click: () => finish(null) });

    try {
      if (mainWindow && !mainWindow.isDestroyed()) {
        if (mainWindow.isMinimized()) mainWindow.restore();
        mainWindow.show();
        mainWindow.focus();
      }
      Menu.buildFromTemplate(items).popup({
        window: mainWindow && !mainWindow.isDestroyed() ? mainWindow : undefined,
        // Menu closed without a choice = cancel. Delay so a click handler runs first.
        callback: () => setTimeout(() => finish(null), 100)
      });
    } catch (err) {
      console.warn('Screen picker failed:', err);
      finish(null);
    }
  });
}

// Keep references to shown notifications: if the JS object is garbage collected,
// its 'click' handler no longer fires. Bounded LRU keyed by tab + tag.
const activeNotifications = new Map();
const MAX_ACTIVE_NOTIFICATIONS = 100;

// Icons supplied by the page (Chat: avatar of the person / space) are downloaded
// in the main process and cached. Only Google image hosts and data:image URLs.
const notificationIconCache = new Map();
const MAX_NOTIFICATION_ICON_CACHE = 100;
const NOTIFICATION_ICON_TIMEOUT_MS = 2500;
const NOTIFICATION_ICON_MAX_BYTES = 2 * 1024 * 1024;
const NOTIFICATION_ICON_MAX_SIZE = 256;

function isAllowedNotificationIconUrl(url) {
  try {
    const u = new URL(url);
    if (u.protocol !== 'https:') return false;
    const host = u.hostname.toLowerCase();
    return (
      host.endsWith('.googleusercontent.com') ||
      host.endsWith('.gstatic.com') ||
      host.endsWith('.ggpht.com') ||
      host === 'google.com' ||
      host.endsWith('.google.com')
    );
  } catch (_) {
    return false;
  }
}

function normalizeNotificationIcon(img) {
  if (!img || img.isEmpty()) return null;
  const { width, height } = img.getSize();
  let sized = img;
  if (width > NOTIFICATION_ICON_MAX_SIZE || height > NOTIFICATION_ICON_MAX_SIZE) {
    const scale = NOTIFICATION_ICON_MAX_SIZE / Math.max(width, height);
    sized = img.resize({
      width: Math.max(1, Math.round(width * scale)),
      height: Math.max(1, Math.round(height * scale)),
      quality: 'best'
    });
  }
  return makeCircularIcon(sized);
}

// Center-crop to a square and apply an anti-aliased circular alpha mask, so avatars
// show up as circles in the desktop notification (like in Chat itself).
function makeCircularIcon(img) {
  try {
    const { width, height } = img.getSize();
    const side = Math.min(width, height);
    if (side <= 0) return img;
    const square =
      width === height
        ? img
        : img.crop({
            x: Math.floor((width - side) / 2),
            y: Math.floor((height - side) / 2),
            width: side,
            height: side
          });
    const { width: w, height: h } = square.getSize();
    const bitmap = Buffer.from(square.toBitmap());
    if (bitmap.length !== w * h * 4) return img;

    const radius = Math.min(w, h) / 2;
    const cx = w / 2;
    const cy = h / 2;
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const dx = x + 0.5 - cx;
        const dy = y + 0.5 - cy;
        const coverage = Math.max(0, Math.min(1, radius - Math.sqrt(dx * dx + dy * dy) + 0.5));
        if (coverage >= 1) continue;
        // Skia bitmaps are premultiplied: scale color channels together with alpha
        const i = (y * w + x) * 4;
        bitmap[i] = Math.round(bitmap[i] * coverage);
        bitmap[i + 1] = Math.round(bitmap[i + 1] * coverage);
        bitmap[i + 2] = Math.round(bitmap[i + 2] * coverage);
        bitmap[i + 3] = Math.round(bitmap[i + 3] * coverage);
      }
    }
    const circle = nativeImage.createFromBitmap(bitmap, { width: w, height: h });
    return circle.isEmpty() ? img : circle;
  } catch (_) {
    return img;
  }
}

function cacheNotificationIcon(url, img) {
  notificationIconCache.delete(url);
  notificationIconCache.set(url, img);
  while (notificationIconCache.size > MAX_NOTIFICATION_ICON_CACHE) {
    notificationIconCache.delete(notificationIconCache.keys().next().value);
  }
}

async function resolveNotificationIcon(url) {
  if (typeof url !== 'string' || !url) return null;

  if (url.startsWith('data:image/')) {
    if (url.length > NOTIFICATION_ICON_MAX_BYTES * 1.4) return null;
    try {
      return normalizeNotificationIcon(nativeImage.createFromDataURL(url));
    } catch (_) {
      return null;
    }
  }

  if (!isAllowedNotificationIconUrl(url)) return null;
  if (notificationIconCache.has(url)) {
    const cached = notificationIconCache.get(url);
    cacheNotificationIcon(url, cached);
    return cached;
  }

  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), NOTIFICATION_ICON_TIMEOUT_MS);
  try {
    // Session fetch carries the user's Google cookies (private avatars).
    // Ask for PNG/JPEG: nativeImage cannot decode WebP/SVG.
    const res = await session.defaultSession.fetch(url, {
      signal: controller.signal,
      headers: { Accept: 'image/png,image/jpeg;q=0.9,*/*;q=0.1' }
    });
    if (!res.ok || (res.url && !isAllowedNotificationIconUrl(res.url))) return null;
    const contentType = (res.headers.get('content-type') || '').toLowerCase();
    if (!contentType.startsWith('image/')) return null;
    const declared = Number(res.headers.get('content-length') || 0);
    if (declared > NOTIFICATION_ICON_MAX_BYTES) return null;
    const buf = Buffer.from(await res.arrayBuffer());
    if (buf.length === 0 || buf.length > NOTIFICATION_ICON_MAX_BYTES) return null;
    const img = normalizeNotificationIcon(nativeImage.createFromBuffer(buf));
    if (img) cacheNotificationIcon(url, img);
    return img;
  } catch (_) {
    return null;
  } finally {
    clearTimeout(timer);
  }
}

async function showCustomNotification({
  title,
  body,
  icon,
  tag,
  silent,
  appId,
  tabId,
  pageNotificationId = null,
  sourceWebContents = null
}) {
  if (!Notification.isSupported()) return;

  const appDef = byId(appId);
  const appName = appDef ? appDef.title : 'Google Suite';

  // Prefer the icon supplied by the web app (Chat: avatar of the conversation),
  // fall back to the clean official app icon (WITHOUT notification dot).
  let notifIcon = await resolveNotificationIcon(icon);
  if (!notifIcon) {
    const iconPath = getAppIconPath(appId, false);
    notifIcon = iconPath;
    try {
      const img = nativeImage.createFromPath(iconPath);
      if (!img.isEmpty()) {
        notifIcon = img;
      }
    } catch (_) {}
  }

  // Format custom title & branding per app
  let displayTitle = title || appName;
  if (appId === 'gmail') {
    displayTitle = title ? `Gmail • ${title}` : 'Nuova email ricevuta';
  } else if (appId === 'chat') {
    displayTitle = title ? `Google Chat • ${title}` : 'Nuovo messaggio in Chat';
  } else if (appId === 'calendar') {
    displayTitle = title ? `Google Calendar • ${title}` : 'Promemoria Google Calendar';
  } else if (appId === 'meet') {
    displayTitle = title ? `Google Meet • ${title}` : 'Google Meet';
  } else if (appId === 'gemini') {
    displayTitle = title ? `Gemini • ${title}` : 'Google Gemini';
  } else if (appDef && !displayTitle.toLowerCase().includes(appDef.title.toLowerCase())) {
    displayTitle = `${appDef.title} • ${displayTitle}`;
  }

  // Let the desktop environment (KDE Plasma / GNOME) manage notification timeout and persist to history tray
  const notification = new Notification({
    title: displayTitle,
    body: body || '',
    icon: notifIcon,
    urgency: 'normal',
    silent: Boolean(silent)
  });

  const key = `${tabId || appId || 'app'}:${tag || pageNotificationId || `${Date.now()}_${Math.random()}`}`;

  // Same tag = same conversation/thread: replace the previous popup instead of stacking
  const previous = activeNotifications.get(key);
  if (previous) {
    activeNotifications.delete(key);
    try {
      previous.close();
    } catch (_) {}
  }
  activeNotifications.set(key, notification);
  while (activeNotifications.size > MAX_ACTIVE_NOTIFICATIONS) {
    activeNotifications.delete(activeNotifications.keys().next().value);
  }

  notification.on('click', () => {
    if (!mainWindow) return;
    if (mainWindow.isMinimized()) mainWindow.restore();
    if (!mainWindow.isVisible()) mainWindow.show();
    mainWindow.focus();

    if (tabId && state.tabs.some((t) => t.id === tabId)) {
      activateTab(tabId);
    } else if (appId) {
      showAndSwitchTo(appId);
    }

    // Forward the click to the page so the web app runs its own onclick
    // (e.g. Google Chat opens the conversation the message belongs to)
    if (pageNotificationId && sourceWebContents && !sourceWebContents.isDestroyed()) {
      try {
        sourceWebContents.send('gapps-notification-event', { id: pageNotificationId, type: 'click' });
      } catch (_) {}
    }
  });

  try {
    notification.show();
  } catch (err) {
    activeNotifications.delete(key);
    console.error('Failed to show notification:', err);
  }
}

function triggerNotificationForApp(appId, title, body) {
  let targetTab = state.tabs.find((t) => t.app === appId);
  if (!targetTab && state.tabs.length > 0) {
    targetTab = state.tabs[0];
  }
  if (targetTab) {
    targetTab.hasNotification = true;
    updateAppBadge();
    broadcastState();
  } else {
    updateAppBadge();
  }
  showCustomNotification({
    title,
    body,
    appId,
    tabId: targetTab ? targetTab.id : null
  });
}

function parseSemver(v) {
  if (!v || typeof v !== 'string') return [0, 0, 0];
  const cleaned = v.trim().replace(/^v/i, '');
  const parts = cleaned.split('.').map((p) => parseInt(p, 10) || 0);
  while (parts.length < 3) parts.push(0);
  return parts;
}

function isNewerVersion(remoteVer, currentVer) {
  const r = parseSemver(remoteVer);
  const c = parseSemver(currentVer);
  for (let i = 0; i < 3; i++) {
    if (r[i] > c[i]) return true;
    if (r[i] < c[i]) return false;
  }
  return false;
}

function checkForAppUpdates(interactive = false) {
  const currentVersion = app.getVersion();
  const repoOwner = 'r-dimajo';
  const repoName = 'google-suite-linux';
  const releasesUrl = `https://github.com/${repoOwner}/${repoName}/releases`;
  const apiUrl = `https://api.github.com/repos/${repoOwner}/${repoName}/releases/latest`;

  const req = https.get(
    apiUrl,
    {
      headers: {
        'User-Agent': `GoogleSuiteLinux/${currentVersion} (Linux; Electron)`
      },
      timeout: 6000
    },
    (res) => {
      if (res.statusCode !== 200) {
        if (interactive && mainWindow && !mainWindow.isDestroyed()) {
          dialog.showMessageBox(mainWindow, {
            type: 'info',
            title: 'Controllo aggiornamenti',
            message: `Versione corrente: v${currentVersion}\nNessun nuovo aggiornamento trovato o archivio rilasci al momento non raggiungibile.`,
            buttons: ['OK']
          });
        }
        res.resume();
        return;
      }

      let rawData = '';
      res.on('data', (chunk) => {
        rawData += chunk;
      });
      res.on('end', () => {
        try {
          const data = JSON.parse(rawData);
          const latestTag = data.tag_name || data.name || '';
          const targetUrl = data.html_url || releasesUrl;

          if (latestTag && isNewerVersion(latestTag, currentVersion)) {
            const displayTag = latestTag.startsWith('v') ? latestTag : `v${latestTag}`;
            const notif = new Notification({
              title: `Google Suite • Aggiornamento disponibile`,
              body: `È disponibile la versione ${displayTag} (versione attuale: v${currentVersion}). Clicca per scaricarla.`,
              icon: nativeImage.createFromPath(ICON_PATH),
              urgency: 'normal'
            });

            notif.on('click', () => {
              safeOpenExternal(targetUrl);
            });

            try {
              notif.show();
            } catch (err) {
              console.warn('Could not show update notification:', err);
            }

            if (interactive && mainWindow && !mainWindow.isDestroyed()) {
              dialog
                .showMessageBox(mainWindow, {
                  type: 'info',
                  title: 'Aggiornamento disponibile',
                  message: `È disponibile una nuova versione di Google Suite: ${displayTag}\n(versione installata: v${currentVersion})`,
                  detail: 'Vuoi aprire la pagina delle release per scaricare il pacchetto aggiornato (.deb / AppImage)?',
                  buttons: ['Apri pagina release', 'Più tardi'],
                  defaultId: 0,
                  cancelId: 1
                })
                .then((result) => {
                  if (result.response === 0) {
                    safeOpenExternal(targetUrl);
                  }
                });
            }
          } else if (interactive && mainWindow && !mainWindow.isDestroyed()) {
            dialog.showMessageBox(mainWindow, {
              type: 'info',
              title: 'Controllo aggiornamenti',
              message: `Google Suite è aggiornato all'ultima versione (v${currentVersion}).`,
              buttons: ['OK']
            });
          }
        } catch (e) {
          console.warn('Failed to parse release response:', e);
        }
      });
    }
  );

  req.on('error', (err) => {
    if (interactive && mainWindow && !mainWindow.isDestroyed()) {
      dialog.showMessageBox(mainWindow, {
        type: 'warning',
        title: 'Controllo aggiornamenti',
        message: 'Impossibile verificare la presenza di aggiornamenti. Verifica la connessione a Internet.',
        buttons: ['OK']
      });
    } else {
      console.warn('Update check failed:', err.message);
    }
  });

  req.on('timeout', () => {
    req.destroy();
  });
}

function createTabView(tab) {
  const isLocalNewTab = tab.url.startsWith('file://');

  const view = new WebContentsView({
    webPreferences: {
      preload: isLocalNewTab
        ? path.join(__dirname, 'preload.js')
        : path.join(__dirname, 'tab-preload.js'),
      contextIsolation: true,
      nodeIntegration: false,
      sandbox: true,
      spellcheck: true,
      backgroundThrottling: false
    }
  });

  // Global hotkeys inside tab contents
  view.webContents.on('before-input-event', (event, input) => {
    if (input.type === 'keyDown' && input.alt && input.shift && input.key.toLowerCase() === 'v') {
      event.preventDefault();
      toggleTabLayout();
      return;
    }
    if (input.type === 'keyDown' && input.alt && input.shift && input.key.toLowerCase() === 's') {
      event.preventDefault();
      showSplitMenu();
      return;
    }

    // Ensure Paste without formatting (Ctrl+Shift+V) works consistently across all web views
    if (input.type === 'keyDown' && input.control && input.shift && input.key.toLowerCase() === 'v') {
      event.preventDefault();
      try {
        view.webContents.pasteAndMatchStyle();
      } catch (_) {
        view.webContents.paste();
      }
    }
  });

  // Link interception: internal Google URLs open inside the shell as tabs;
  // external URLs open in default system browser
  view.webContents.setWindowOpenHandler(({ url }) => {
    if (!url || url === 'about:blank') {
      return { action: 'deny' };
    }
    const targetUrl = unwrapGoogleUrl(url);
    if (isInternal(targetUrl)) {
      createTab(targetUrl, null, true);
      return { action: 'deny' };
    }
    safeOpenExternal(targetUrl);
    return { action: 'deny' };
  });

  const handleExternalNav = (event, navUrl) => {
    if (!navUrl || navUrl === 'about:blank') return;
    const targetUrl = unwrapGoogleUrl(navUrl);
    if (!isInternal(targetUrl)) {
      event.preventDefault();
      safeOpenExternal(targetUrl);

      // If this tab was newly opened and its destination was external,
      // close this empty orphan tab instead of leaving it stuck open
      if (!tab.pinned && !tab.locked) {
        const canGoBack = view.webContents.canGoBack();
        const currentUrl = view.webContents.getURL();
        if (!canGoBack || !currentUrl || currentUrl === 'about:blank' || currentUrl.startsWith('file://')) {
          setTimeout(() => {
            if (tabViews.has(tab.id) && !view.webContents.canGoBack()) {
              closeTab(tab.id);
            }
          }, 30);
        }
      }
    }
  };

  view.webContents.on('will-navigate', handleExternalNav);
  view.webContents.on('will-redirect', handleExternalNav);

  // Track active URL and app (both full navigation and SPA in-page hash/history navigation)
  const onUrlChange = (url) => {
    if (!url) return;
    tab.url = url;
    if (url.startsWith('file://')) {
      tab.app = 'newtab';
      tab.title = 'New Tab';
    } else {
      const detected = detectApp(url);
      if (detected && detected.id !== tab.app) {
        tab.app = detected.id;
      }
    }
    saveState();
    broadcastState();
  };

  view.webContents.on('did-navigate', (_event, url) => onUrlChange(url));
  view.webContents.on('did-navigate-in-page', (_event, url) => onUrlChange(url));

  // Update tab title. Unread counts are NOT parsed here: they come only from the
  // tab-preload observer (tab-unread-count), otherwise the two sources fight and
  // badges disappear on their own (e.g. Chat title "Mario Rossi - Chat").
  view.webContents.on('page-title-updated', (event, title) => {
    event.preventDefault();
    if (title) {
      tab.title = title;

      if (tab.id === state.active && mainWindow && !mainWindow.isDestroyed()) {
        const displayTitle = tab.customTitle || title;
        mainWindow.setTitle(`${displayTitle} — Google Suite`);
      }
      saveState();
      broadcastState();
    }
  });

  // Page (re)loaded: push current visibility so the new document starts in sync
  view.webContents.on('dom-ready', () => {
    sendTabVisibility(tab.id, true);
  });

  // Renderer crash / OOM kill: without this, Chat/Gmail die silently and stop notifying
  view.webContents.on('render-process-gone', (_event, details) => {
    if (details && details.reason === 'clean-exit') return;
    console.warn(`[Google Suite] Tab ${tab.app} renderer gone (${details && details.reason}), reloading`);
    setTimeout(() => {
      if (tabViews.get(tab.id) === view && !view.webContents.isDestroyed()) {
        try {
          view.webContents.reload();
        } catch (_) {}
      }
    }, 3000);
  });

  // Audio indicators & mute detection
  view.webContents.on('media-started-playing', () => {
    tab.isAudible = true;
    broadcastState();
  });

  view.webContents.on('media-paused', () => {
    tab.isAudible = view.webContents.isCurrentlyAudible();
    broadcastState();
  });

  // Context menu handling (images, links, text editing, spellcheck)
  view.webContents.on('context-menu', (_event, params) => {
    const menuItems = [];

    // Spellcheck suggestions
    if (params.misspelledWord) {
      if (params.dictionarySuggestions && params.dictionarySuggestions.length > 0) {
        params.dictionarySuggestions.forEach((suggestion) => {
          menuItems.push({
            label: suggestion,
            click: () => view.webContents.replaceMisspelling(suggestion)
          });
        });
      } else {
        menuItems.push({
          label: 'No Guesses Found',
          enabled: false
        });
      }
      menuItems.push({ type: 'separator' });
    }

    // Image actions
    if (params.mediaType === 'image' || params.hasImageContents) {
      menuItems.push({
        label: 'Copy Image',
        click: () => view.webContents.copyImageAt(params.x, params.y)
      });
      if (params.srcURL) {
        menuItems.push({
          label: 'Copy Image Address',
          click: () => clipboard.writeText(params.srcURL)
        });
        menuItems.push({
          label: 'Save Image As…',
          click: () => view.webContents.downloadURL(params.srcURL)
        });
      }
      menuItems.push({ type: 'separator' });
    }

    // Link actions
    if (params.linkURL) {
      const targetUrl = unwrapGoogleUrl(params.linkURL);
      menuItems.push({
        label: 'Open Link in Default Browser',
        click: () => safeOpenExternal(targetUrl)
      });
      if (isInternal(targetUrl)) {
        menuItems.push({
          label: 'Open Link in New Tab',
          click: () => createTab(targetUrl, null, true)
        });
      }
      menuItems.push({
        label: 'Copy Link Address',
        click: () => clipboard.writeText(targetUrl)
      });
      menuItems.push({ type: 'separator' });
    }

    // Selection / Edit actions (always include paste and copy actions for rich web editors like Google Docs)
    if (params.isEditable) {
      menuItems.push({ role: 'undo' });
      menuItems.push({ role: 'redo' });
      menuItems.push({ type: 'separator' });
      menuItems.push({ role: 'cut' });
      menuItems.push({ role: 'copy' });
      menuItems.push({ role: 'paste' });
      menuItems.push({ role: 'pasteAndMatchStyle', label: 'Paste as plain text' });
      menuItems.push({ role: 'selectAll' });
    } else if (params.selectionText && params.selectionText.trim().length > 0) {
      menuItems.push({ role: 'copy' });
      menuItems.push({ role: 'selectAll' });
    } else if (isInternal(tab.url)) {
      // In web apps like Google Docs where canvas rendering is used, params.isEditable may be false
      menuItems.push({ role: 'cut' });
      menuItems.push({ role: 'copy' });
      menuItems.push({ role: 'paste' });
      menuItems.push({ role: 'pasteAndMatchStyle', label: 'Paste as plain text' });
      menuItems.push({ role: 'selectAll' });
    }

    // Clean up trailing or consecutive separators
    const cleaned = [];
    for (let i = 0; i < menuItems.length; i++) {
      const item = menuItems[i];
      if (item.type === 'separator') {
        if (cleaned.length === 0 || cleaned[cleaned.length - 1].type === 'separator') {
          continue;
        }
      }
      cleaned.push(item);
    }
    if (cleaned.length > 0 && cleaned[cleaned.length - 1].type === 'separator') {
      cleaned.pop();
    }

    if (cleaned.length > 0) {
      const contextMenu = Menu.buildFromTemplate(cleaned);
      contextMenu.popup({ window: mainWindow });
    }
  });

  view.webContents.loadURL(tab.url);
  return view;
}

function createTab(url = null, appId = null, activate = true, pinned = false, locked = null) {
  const isNewTab = !url && !appId;
  const rawTargetUrl = isNewTab ? NEW_TAB_URL : (url || (byId(appId) ? byId(appId).url : NEW_TAB_URL));
  const targetUrl = isNewTab ? rawTargetUrl : unwrapGoogleUrl(rawTargetUrl);

  // If an external URL is passed to createTab, open it in default browser instead of creating an empty tab
  if (!isNewTab && !isInternal(targetUrl)) {
    safeOpenExternal(targetUrl);
    return null;
  }

  const appDef = appId ? byId(appId) : (detectApp(targetUrl) || null);
  const detectedAppId = isNewTab ? 'newtab' : (appDef ? appDef.id : 'web');
  const isLocked = locked !== null ? Boolean(locked) : ['gmail', 'chat', 'calendar'].includes(detectedAppId);

  const tabId = 'tab_' + Date.now() + '_' + Math.random().toString(36).slice(2, 6);
  const tab = {
    id: tabId,
    app: detectedAppId,
    title: isNewTab ? 'New Tab' : (appDef ? appDef.title : 'Google'),
    url: targetUrl,
    pinned: Boolean(pinned),
    locked: isLocked,
    unreadCount: 0,
    isAudible: false,
    isMuted: false,
    lastAccessed: Date.now()
  };

  if (pinned) {
    const pinnedCount = state.tabs.filter((t) => t.pinned).length;
    state.tabs.splice(pinnedCount, 0, tab);
  } else {
    state.tabs.push(tab);
  }

  if (activate) {
    activateTab(tabId);
  } else {
    // If not activating, create background view so notifications work
    try {
      const view = createTabView(tab);
      tabViews.set(tabId, view);
    } catch (_) {}
    saveState();
    broadcastState();
  }
  return tabId;
}

function openNewTab() {
  return createTab(null, null, true, false);
}

function navigateCurrentTab(url, appId = null) {
  if (!state.active) return;
  const tab = state.tabs.find((t) => t.id === state.active);
  if (!tab) return;

  const targetUrl = unwrapGoogleUrl(url);
  if (!isInternal(targetUrl)) {
    safeOpenExternal(targetUrl);
    return;
  }

  const appDef = appId ? byId(appId) : (detectApp(targetUrl) || null);
  tab.url = targetUrl;
  tab.app = appDef ? appDef.id : (tab.app !== 'newtab' ? tab.app : 'web');
  tab.title = appDef ? appDef.title : 'Loading...';
  tab.lastAccessed = Date.now();

  let view = tabViews.get(tab.id);
  if (view) {
    // If transitioning from local newtab to remote Google app, recreate view for proper preload & sandbox
    if (view.webContents.getURL().startsWith('file://') && !url.startsWith('file://')) {
      if (mainWindow && !mainWindow.isDestroyed()) {
        try { mainWindow.contentView.removeChildView(view); } catch (_) {}
      }
      try { view.webContents.close(); } catch (_) {}
      tabViews.delete(tab.id);

      view = createTabView(tab);
      tabViews.set(tab.id, view);
      if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.contentView.addChildView(view);
      }
      updateBounds();
      view.webContents.focus();
    } else {
      view.webContents.loadURL(url);
    }
  }

  saveState();
  broadcastState();
}

function setSplitView(tabId = null, direction = 'horizontal', ratio = 0.5) {
  if (!tabId || tabId === state.active) {
    // If no tabId or same as active tab, disable split view
    if (state.split && state.split.enabled && state.split.tabId && tabViews.has(state.split.tabId)) {
      const prevSecondary = tabViews.get(state.split.tabId);
      if (mainWindow && !mainWindow.isDestroyed() && state.split.tabId !== state.active) {
        try { mainWindow.contentView.removeChildView(prevSecondary); } catch (_) {}
      }
    }
    state.split = {
      enabled: false,
      tabId: null,
      direction: 'horizontal',
      ratio: 0.5
    };
  } else {
    const secondaryTab = state.tabs.find((t) => t.id === tabId);
    if (!secondaryTab) return;

    // Detach old secondary if different
    if (state.split && state.split.tabId && state.split.tabId !== tabId && tabViews.has(state.split.tabId)) {
      const prevSecondary = tabViews.get(state.split.tabId);
      if (mainWindow && !mainWindow.isDestroyed() && state.split.tabId !== state.active) {
        try { mainWindow.contentView.removeChildView(prevSecondary); } catch (_) {}
      }
    }

    // Lazy load secondary tab view
    let secView = tabViews.get(tabId);
    if (!secView) {
      secView = createTabView(secondaryTab);
      tabViews.set(tabId, secView);
    }
    if (mainWindow && !mainWindow.isDestroyed()) {
      try { mainWindow.contentView.addChildView(secView); } catch (_) {}
    }

    secondaryTab.lastAccessed = Date.now();

    state.split = {
      enabled: true,
      tabId,
      direction: direction === 'vertical' ? 'vertical' : 'horizontal',
      ratio: typeof ratio === 'number' ? Math.max(0.2, Math.min(0.8, ratio)) : 0.5
    };
  }

  updateBounds();
  saveState();
  broadcastState();
  syncTabVisibility();
}

function closeSplitView() {
  setSplitView(null);
}

function activateTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;

  tab.lastAccessed = Date.now();

  const prevActiveId = state.active;
  // If moving away from a tab that is not the secondary split tab, detach it
  if (prevActiveId && prevActiveId !== tabId && tabViews.has(prevActiveId)) {
    const isSplitSec = state.split && state.split.enabled && state.split.tabId === prevActiveId;
    if (!isSplitSec && mainWindow && !mainWindow.isDestroyed()) {
      const prevView = tabViews.get(prevActiveId);
      try {
        mainWindow.contentView.removeChildView(prevView);
      } catch (_) {}
    }
  }

  // If activating the tab that is currently secondary in split view, close split view or swap
  if (state.split && state.split.enabled && state.split.tabId === tabId) {
    if (prevActiveId && prevActiveId !== tabId) {
      // Swap: make previous active the new secondary split tab
      state.split.tabId = prevActiveId;
    } else {
      state.split.enabled = false;
      state.split.tabId = null;
    }
  }

  // Lazy instantiate tab view if not yet loaded in background
  let view = tabViews.get(tabId);
  if (!view) {
    view = createTabView(tab);
    tabViews.set(tabId, view);
  }

  if (mainWindow && !mainWindow.isDestroyed()) {
    try {
      mainWindow.contentView.addChildView(view);
    } catch (_) {}
  }

  state.active = tabId;
  tab.lastAccessed = Date.now();
  if (view) {
    try {
      const liveUrl = view.webContents.getURL();
      if (liveUrl && !liveUrl.startsWith('file://') && liveUrl !== 'about:blank' && tab.url !== liveUrl) {
        tab.url = liveUrl;
      }
    } catch (_) {}
  }
  if (mainWindow && !mainWindow.isDestroyed()) {
    const displayTitle = tab.customTitle || tab.title || 'Google Suite';
    mainWindow.setTitle(`${displayTitle} — Google Suite`);
  }

  updateBounds();
  try {
    view.webContents.focus();
  } catch (_) {}

  saveState();
  broadcastState();
  syncTabVisibility();
}

function closeTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab || tab.pinned || tab.locked) return;

  const index = state.tabs.findIndex((t) => t.id === tabId);
  if (index === -1) return;

  if (tabViews.has(tabId)) {
    const view = tabViews.get(tabId);
    if (mainWindow && !mainWindow.isDestroyed()) {
      try {
        mainWindow.contentView.removeChildView(view);
      } catch (_) {}
    }
    try {
      view.webContents.close();
    } catch (_) {}
    tabViews.delete(tabId);
  }

  state.tabs.splice(index, 1);
  updateAppBadge();

  // If closed tab was the secondary split view tab, reset split
  if (state.split && state.split.tabId === tabId) {
    state.split.enabled = false;
    state.split.tabId = null;
  }

  if (state.tabs.length === 0) {
    openNewTab();
    return;
  }

  if (state.active === tabId) {
    const nextIndex = Math.min(index, state.tabs.length - 1);
    activateTab(state.tabs[nextIndex].id);
  } else {
    saveState();
    broadcastState();
    syncTabVisibility();
  }
}

function setTabCustomTitle(tabId, customTitle) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;
  tab.customTitle = customTitle && customTitle.trim() ? customTitle.trim() : null;
  if (tab.id === state.active && mainWindow && !mainWindow.isDestroyed()) {
    const displayTitle = tab.customTitle || tab.title || 'Google Suite';
    mainWindow.setTitle(`${displayTitle} — Google Suite`);
  }
  saveState();
  broadcastState();
}

function promptRenameTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;

  const currentName = tab.customTitle || tab.title || '';
  const promptWin = new BrowserWindow({
    parent: mainWindow,
    modal: true,
    width: 440,
    height: 200,
    resizable: false,
    minimizable: false,
    maximizable: false,
    title: 'Rename Tab',
    backgroundColor: '#202124',
    autoHideMenuBar: true,
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: true
    }
  });

  // Escape '<' so a tab title containing </script> cannot break out of the inline script
  const escapedCurrent = JSON.stringify(currentName).replace(/</g, '\\u003c');
  const html = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <style>
    * { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      background: #202124;
      color: #e8eaed;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Noto Sans", Ubuntu, Cantarell, sans-serif;
      padding: 20px;
      user-select: none;
      -webkit-user-select: none;
    }
    h3 { font-size: 14px; font-weight: 500; margin-bottom: 8px; color: #fff; }
    p { font-size: 12px; color: #9aa0a6; margin-bottom: 14px; }
    input {
      width: 100%;
      height: 36px;
      background: #292a2d;
      border: 1px solid #5f6368;
      border-radius: 6px;
      padding: 0 12px;
      color: #fff;
      font-size: 13px;
      outline: none;
    }
    input:focus {
      border-color: #8ab4f8;
      box-shadow: 0 0 0 1px #8ab4f8;
    }
    .buttons {
      margin-top: 18px;
      display: flex;
      justify-content: flex-end;
      gap: 10px;
    }
    button {
      padding: 8px 16px;
      border-radius: 6px;
      font-size: 12px;
      font-weight: 500;
      cursor: pointer;
      border: 1px solid transparent;
      outline: none;
    }
    .btn-cancel {
      background: rgba(255, 255, 255, 0.08);
      color: #e8eaed;
    }
    .btn-cancel:hover {
      background: rgba(255, 255, 255, 0.14);
    }
    .btn-save {
      background: #8ab4f8;
      color: #202124;
    }
    .btn-save:hover {
      background: #aecbfa;
    }
  </style>
</head>
<body>
  <h3>Rename Tab</h3>
  <p>Enter a custom title (leave empty to reset to page title):</p>
  <input type="text" id="nameInput" autofocus />
  <div class="buttons">
    <button class="btn-cancel" id="btnCancel">Cancel</button>
    <button class="btn-save" id="btnSave">Save</button>
  </div>
  <script>
    const input = document.getElementById('nameInput');
    input.value = ${escapedCurrent};
    input.focus();
    input.select();

    function save() {
      document.title = 'action:save:' + encodeURIComponent(input.value);
    }
    function cancel() {
      document.title = 'action:cancel';
    }

    document.getElementById('btnSave').addEventListener('click', save);
    document.getElementById('btnCancel').addEventListener('click', cancel);
    window.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') save();
      else if (e.key === 'Escape') cancel();
    });
  </script>
</body>
</html>`;

  promptWin.loadURL('data:text/html;charset=utf-8,' + encodeURIComponent(html));

  promptWin.on('page-title-updated', (e, title) => {
    e.preventDefault();
    if (!title) return;
    if (title === 'action:cancel') {
      try { promptWin.close(); } catch (_) {}
    } else if (title.startsWith('action:save:')) {
      const val = decodeURIComponent(title.slice('action:save:'.length));
      setTabCustomTitle(tabId, val);
      try { promptWin.close(); } catch (_) {}
    }
  });
}

function toggleLockTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;
  tab.locked = !tab.locked;
  saveState();
  broadcastState();
}

function togglePinTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;

  tab.pinned = !tab.pinned;
  const currentIdx = state.tabs.findIndex((t) => t.id === tabId);
  const [moved] = state.tabs.splice(currentIdx, 1);

  if (tab.pinned) {
    const pinnedCount = state.tabs.filter((t) => t.pinned).length;
    state.tabs.splice(pinnedCount, 0, moved);
  } else {
    const pinnedCount = state.tabs.filter((t) => t.pinned).length;
    state.tabs.splice(pinnedCount, 0, moved);
  }

  saveState();
  broadcastState();
}

function toggleMuteTab(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab || !tabViews.has(tabId)) return;

  const view = tabViews.get(tabId);
  const nextMuted = !view.webContents.isAudioMuted();
  view.webContents.setAudioMuted(nextMuted);
  tab.isMuted = nextMuted;
  broadcastState();
}

function showAppMenu() {
  const template = APPS.map((a) => ({
    label: a.title,
    click: () => createTab(a.url, a.id, true)
  }));
  const menu = Menu.buildFromTemplate(template);
  menu.popup({ window: mainWindow });
}

function showTabMenu(tabId) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;

  const otherTabs = state.tabs.filter((t) => t.id !== tabId);
  const isCurrentlySplit = state.split && state.split.enabled && (state.split.tabId === tabId || state.active === tabId);

  const splitSubmenu = otherTabs.length === 0 ? [] : [
    {
      label: 'Side-by-side (Right)',
      submenu: otherTabs.map((ot) => ({
        label: ot.customTitle || ot.title,
        click: () => {
          if (state.active !== tabId) activateTab(tabId);
          setSplitView(ot.id, 'horizontal', 0.5);
        }
      }))
    },
    {
      label: 'Stacked (Bottom)',
      submenu: otherTabs.map((ot) => ({
        label: ot.customTitle || ot.title,
        click: () => {
          if (state.active !== tabId) activateTab(tabId);
          setSplitView(ot.id, 'vertical', 0.5);
        }
      }))
    }
  ];

  if (isCurrentlySplit) {
    splitSubmenu.unshift({
      label: 'Close split view',
      click: () => closeSplitView()
    }, { type: 'separator' });
  }

  const template = [
    {
      label: tab.locked ? '🔓 Unlock tab (Allow closing)' : '🔒 Lock tab (Prevent accidental closing)',
      click: () => toggleLockTab(tabId)
    },
    {
      label: tab.pinned ? 'Unpin tab' : 'Pin tab',
      click: () => togglePinTab(tabId)
    },
    {
      label: 'Rename tab…',
      click: () => promptRenameTab(tabId)
    },
    {
      label: tab.isMuted ? 'Unmute tab audio' : 'Mute tab audio',
      enabled: Boolean(tab.isAudible || tab.isMuted),
      click: () => toggleMuteTab(tabId)
    },
    { type: 'separator' },
    {
      label: 'Split view',
      submenu: splitSubmenu.length > 0 ? splitSubmenu : [{ label: 'No other tabs available', enabled: false }]
    },
    { type: 'separator' },
    {
      label: 'Open in default browser',
      click: () => {
        safeOpenExternal(tab.url);
        if (!tab.pinned && !tab.locked) closeTab(tabId);
      }
    },
    {
      label: 'Reload tab',
      click: () => {
        if (tabViews.has(tabId)) {
          tabViews.get(tabId).webContents.reload();
        }
      }
    },
    {
      label: 'Duplicate tab',
      click: () => createTab(tab.url, tab.app, true)
    },
    { type: 'separator' },
    {
      label: settings.tab_layout === 'vertical' ? 'Switch to top tabs (Horizontal)' : 'Switch to side tabs (Vertical)',
      click: () => toggleTabLayout()
    },
    { type: 'separator' },
    {
      label: 'Close tab',
      enabled: !tab.pinned && !tab.locked,
      click: () => closeTab(tabId)
    },
    {
      label: 'Close other tabs',
      enabled: state.tabs.filter((t) => !t.pinned && !t.locked).length > 1,
      click: () => {
        const toClose = state.tabs.filter((t) => t.id !== tabId && !t.pinned && !t.locked).map((t) => t.id);
        toClose.forEach((id) => closeTab(id));
      }
    }
  ];

  const menu = Menu.buildFromTemplate(template);
  menu.popup({ window: mainWindow });
}

function showSplitMenu() {
  const activeTabId = state.active;
  const activeTab = state.tabs.find((t) => t.id === activeTabId);
  const otherTabs = state.tabs.filter((t) => t.id !== activeTabId);
  const isCurrentlySplit = Boolean(state.split && state.split.enabled && state.split.tabId);

  const template = [];

  if (isCurrentlySplit) {
    const secTab = state.tabs.find((t) => t.id === state.split.tabId);
    const secTitle = secTab ? (secTab.customTitle || secTab.title) : 'Secondary tab';
    template.push({
      label: `Close split view (${secTitle})`,
      click: () => closeSplitView()
    });
    template.push({
      label: state.split.direction === 'vertical' ? 'Switch to side-by-side (Right)' : 'Switch to stacked (Bottom)',
      click: () => setSplitView(state.split.tabId, state.split.direction === 'vertical' ? 'horizontal' : 'vertical', state.split.ratio)
    });
    template.push({
      label: 'Reset split size (50 / 50)',
      click: () => setSplitView(state.split.tabId, state.split.direction, 0.5)
    });
    template.push({ type: 'separator' });
  }

  if (otherTabs.length === 0) {
    template.push({
      label: 'Open another tab first to split view',
      enabled: false
    });
  } else {
    template.push({
      label: 'Split Side-by-side (Right) with…',
      submenu: otherTabs.map((ot) => ({
        label: ot.customTitle || ot.title,
        click: () => setSplitView(ot.id, 'horizontal', 0.5)
      }))
    });
    template.push({
      label: 'Split Stacked (Bottom) with…',
      submenu: otherTabs.map((ot) => ({
        label: ot.customTitle || ot.title,
        click: () => setSplitView(ot.id, 'vertical', 0.5)
      }))
    });
  }

  const menu = Menu.buildFromTemplate(template);
  menu.popup({ window: mainWindow });
}

function setTabLayout(layout) {
  settings.tab_layout = layout === 'vertical' ? 'vertical' : 'horizontal';
  saveSettings();
  updateBounds();
  broadcastState();
}

function toggleTabLayout() {
  setTabLayout(settings.tab_layout === 'vertical' ? 'horizontal' : 'vertical');
}

function showSettingsMenu() {
  const detected = getDesktopEnvironment() === 'gnome' ? 'GNOME' : 'KDE Plasma';
  const template = [
    {
      label: 'Tab layout',
      submenu: [
        {
          label: 'Top (Horizontal)',
          type: 'radio',
          checked: settings.tab_layout !== 'vertical',
          click: () => setTabLayout('horizontal')
        },
        {
          label: 'Side (Vertical)',
          type: 'radio',
          checked: settings.tab_layout === 'vertical',
          click: () => setTabLayout('vertical')
        }
      ]
    },
    {
      label: 'Desktop theme',
      submenu: [
        {
          label: `Auto-detect (${detected})`,
          type: 'radio',
          checked: !settings.desktop_theme || settings.desktop_theme === 'auto',
          click: () => setDesktopTheme('auto')
        },
        {
          label: 'GNOME (Libadwaita)',
          type: 'radio',
          checked: settings.desktop_theme === 'gnome',
          click: () => setDesktopTheme('gnome')
        },
        {
          label: 'KDE Plasma (Breeze)',
          type: 'radio',
          checked: settings.desktop_theme === 'kde',
          click: () => setDesktopTheme('kde')
        }
      ]
    },
    {
      label: 'On window close',
      submenu: [
        {
          label: 'Keep running in background (Tray / Dock)',
          type: 'radio',
          checked: settings.close_action !== 'quit',
          click: () => {
            settings.close_action = 'tray';
            saveSettings();
          }
        },
        {
          label: 'Quit application',
          type: 'radio',
          checked: settings.close_action === 'quit',
          click: () => {
            settings.close_action = 'quit';
            saveSettings();
          }
        }
      ]
    },
    { type: 'separator' },
    {
      label: 'Launch at startup',
      type: 'checkbox',
      checked: settings.open_at_startup,
      click: (item) => {
        settings.open_at_startup = item.checked;
        saveSettings();
        manageAutostart(settings.open_at_startup);
        try {
          app.setLoginItemSettings({
            openAtLogin: settings.open_at_startup
          });
        } catch (_) {}
      }
    },
    {
      label: 'Start minimized to tray',
      type: 'checkbox',
      checked: settings.start_minimized,
      click: (item) => {
        settings.start_minimized = item.checked;
        saveSettings();
      }
    },
    {
      label: 'Memory Saver (suspend inactive background tabs)',
      type: 'checkbox',
      checked: settings.memory_saver,
      click: (item) => {
        settings.memory_saver = item.checked;
        saveSettings();
      }
    },
    { type: 'separator' },
    {
      label: 'Test Google Chat notification...',
      click: () => {
        triggerNotificationForApp('chat', 'Alex Miller', 'Hello! Test notification for Google Chat.');
      }
    },
    {
      label: 'Test Gmail notification...',
      click: () => {
        triggerNotificationForApp('gmail', 'Google Suite Team', 'Test notification for Gmail.');
      }
    },
    {
      label: 'Test Google Gemini notification...',
      click: () => {
        triggerNotificationForApp('gemini', 'Google Gemini', 'Test notification with Gemini star.');
      }
    },
    {
      label: 'Clear cache...',
      click: async () => {
        await session.defaultSession.clearCache();
        dialog.showMessageBox(mainWindow, {
          type: 'info',
          title: 'Cache',
          message: 'Cache cleared successfully.',
          buttons: ['OK']
        });
      }
    },
    {
      label: 'Check for updates…',
      click: () => {
        checkForAppUpdates(true);
      }
    },
    { type: 'separator' },
    {
      label: 'Quit Google Suite',
      click: () => {
        app.isQuitting = true;
        app.quit();
      }
    }
  ];

  const menu = Menu.buildFromTemplate(template);
  menu.popup({ window: mainWindow });
}

function toggleWindow() {
  if (!mainWindow) return;
  if (mainWindow.isVisible()) {
    mainWindow.hide();
  } else {
    mainWindow.show();
    mainWindow.focus();
  }
  updateTrayMenu();
}

function showAndSwitchTo(appId) {
  if (!mainWindow) return;
  mainWindow.show();
  mainWindow.focus();
  updateTrayMenu();
  const existing = state.tabs.find((t) => t.app === appId);
  if (existing) {
    activateTab(existing.id);
  } else {
    const appDef = byId(appId);
    if (appDef) createTab(appDef.url, appDef.id, true);
  }
}

function updateTrayMenu() {
  if (!tray) return;
  const isVisible = mainWindow && !mainWindow.isDestroyed() && mainWindow.isVisible();

  // Nested submenu with all 11 apps
  const allAppsSubmenu = APPS.map((app) => {
    const iconPath = getAppIconPath(app.id);
    let itemIcon = null;
    try {
      const img = nativeImage.createFromPath(iconPath);
      if (!img.isEmpty()) {
        itemIcon = img.resize({ width: 16, height: 16 });
      }
    } catch (_) {}

    return {
      label: `${app.title} — ${app.description}`,
      icon: itemIcon || undefined,
      click: () => showAndSwitchTo(app.id)
    };
  });

  const contextMenu = Menu.buildFromTemplate([
    {
      label: isVisible ? 'Hide Google Suite' : 'Show Google Suite',
      accelerator: 'CmdOrCtrl+Alt+G',
      click: toggleWindow
    },
    {
      label: 'New tab (App grid)...',
      click: () => {
        if (!mainWindow.isVisible()) mainWindow.show();
        mainWindow.focus();
        openNewTab();
      }
    },
    { type: 'separator' },
    {
      label: 'Google Apps',
      submenu: allAppsSubmenu
    },
    { type: 'separator' },
    {
      label: 'Quit Google Suite',
      click: () => {
        app.isQuitting = true;
        app.quit();
      }
    }
  ]);

  tray.setContextMenu(contextMenu);
}

function createTray() {
  try {
    const icon = nativeImage.createFromPath(getTrayIconPath());
    tray = new Tray(icon);
    tray.setToolTip('Google Suite');

    updateTrayMenu();

    tray.on('click', toggleWindow);
    tray.on('double-click', toggleWindow);
    tray.on('middle-click', toggleWindow);
  } catch (err) {
    console.warn('[Google Suite] System tray not available in this environment:', err.message);
  }
}

function handleArgv(argv) {
  for (const arg of argv) {
    if (!arg || arg.startsWith('-')) continue;
    if (arg.startsWith('http://') || arg.startsWith('https://')) {
      createTab(arg, null, true);
      return;
    }
    if (arg.startsWith('mailto:')) {
      const email = arg.replace(/^mailto:/, '');
      const gmailUrl = `https://mail.google.com/mail/?view=cm&fs=1&to=${encodeURIComponent(email)}`;
      createTab(gmailUrl, 'gmail', true);
      return;
    }
    const found = byId(arg.toLowerCase());
    if (found) {
      showAndSwitchTo(found.id);
      return;
    }
  }
}

// Background tab hibernation for memory saving (> 30 min inactive)
// Note: Communication apps (Gmail, Chat, Calendar, Meet) and pinned tabs are NEVER hibernated!
setInterval(() => {
  if (!settings.memory_saver) return;
  const now = Date.now();
  const THIRTY_MINUTES = 30 * 60 * 1000;
  const NEVER_HIBERNATE = ['gmail', 'chat', 'calendar', 'meet'];

  state.tabs.forEach((tab) => {
    if (
      tab.id !== state.active &&
      !tab.pinned &&
      !tab.locked &&
      !tab.isAudible &&
      !NEVER_HIBERNATE.includes(tab.app) &&
      tabViews.has(tab.id) &&
      tab.lastAccessed &&
      now - tab.lastAccessed > THIRTY_MINUTES
    ) {
      const view = tabViews.get(tab.id);
      try {
        if (mainWindow && !mainWindow.isDestroyed()) {
          mainWindow.contentView.removeChildView(view);
        }
        view.webContents.close();
      } catch (_) {}
      tabViews.delete(tab.id);
    }
  });
}, 5 * 60 * 1000);

// IPC Handlers
ipcMain.handle('get-state', () => {
  // Sync live webContents URLs if available
  state.tabs.forEach((t) => {
    if (tabViews.has(t.id)) {
      try {
        const liveUrl = tabViews.get(t.id).webContents.getURL();
        if (liveUrl && !liveUrl.startsWith('file://') && liveUrl !== 'about:blank') {
          t.url = liveUrl;
        }
      } catch (_) {}
    }
  });

  return {
    tabs: state.tabs.map((t) => ({
      id: t.id,
      app: t.app,
      title: t.customTitle || t.title,
      customTitle: t.customTitle || null,
      url: t.url,
      pinned: Boolean(t.pinned),
      locked: Boolean(t.locked),
      unreadCount: t.unreadCount || 0,
      hasNotification: Boolean(t.hasNotification),
      isAudible: Boolean(t.isAudible),
      isMuted: Boolean(t.isMuted)
    })),
    active: state.active,
    split: state.split,
    apps: APPS,
    layout: settings.tab_layout || 'horizontal',
    theme: getEffectiveTheme()
  };
});

ipcMain.handle('get-apps', () => APPS);
ipcMain.handle('open-new-tab', () => openNewTab());
ipcMain.handle('navigate-current-tab', (_event, { url, appId }) =>
  navigateCurrentTab(url, appId)
);
ipcMain.handle('activate-tab', (_event, id) => activateTab(id));
ipcMain.handle('close-tab', (_event, id) => closeTab(id));
ipcMain.handle('toggle-lock-tab', (_event, id) => toggleLockTab(id));
ipcMain.handle('toggle-pin-tab', (_event, id) => togglePinTab(id));
ipcMain.handle('set-tab-custom-title', (_event, { id, customTitle }) => setTabCustomTitle(id, customTitle));
ipcMain.handle('prompt-rename-tab', (_event, id) => promptRenameTab(id));
ipcMain.handle('toggle-mute-tab', (_event, id) => toggleMuteTab(id));
ipcMain.handle('set-tab-layout', (_event, layout) => setTabLayout(layout));
ipcMain.handle('toggle-tab-layout', () => toggleTabLayout());
ipcMain.handle('set-desktop-theme', (_event, theme) => setDesktopTheme(theme));
ipcMain.handle('set-split-view', (_event, { tabId, direction, ratio }) => setSplitView(tabId, direction, ratio));
ipcMain.handle('close-split-view', () => closeSplitView());
ipcMain.handle('show-split-menu', () => showSplitMenu());

ipcMain.handle('move-tab', (_event, { sourceId, targetId, dropAfter }) => {
  const sourceIndex = state.tabs.findIndex((t) => t.id === sourceId);
  const targetIndex = state.tabs.findIndex((t) => t.id === targetId);
  if (sourceIndex === -1 || targetIndex === -1 || sourceIndex === targetIndex) return;

  const [movedTab] = state.tabs.splice(sourceIndex, 1);
  const newTargetIndex = state.tabs.findIndex((t) => t.id === targetId);
  const insertIndex = dropAfter ? newTargetIndex + 1 : newTargetIndex;
  state.tabs.splice(insertIndex, 0, movedTab);

  saveState();
  broadcastState();
});

ipcMain.handle('move-tab-to-end', (_event, sourceId) => {
  const sourceIndex = state.tabs.findIndex((t) => t.id === sourceId);
  if (sourceIndex === -1) return;
  const [movedTab] = state.tabs.splice(sourceIndex, 1);
  state.tabs.push(movedTab);

  saveState();
  broadcastState();
});

ipcMain.handle('reload-active', () => {
  if (state.active && tabViews.has(state.active)) {
    tabViews.get(state.active).webContents.reload();
  }
});
ipcMain.handle('show-app-menu', () => showAppMenu());
ipcMain.handle('show-tab-menu', (_event, id) => showTabMenu(id));
ipcMain.handle('show-settings-menu', () => showSettingsMenu());

function findTabBySender(sender) {
  if (!sender) return null;
  for (const [id, view] of tabViews.entries()) {
    if (view && !view.webContents.isDestroyed() && view.webContents.id === sender.id) {
      return state.tabs.find((t) => t.id === id) || null;
    }
  }
  return null;
}

// Initial page visibility requested synchronously by tab-preload.js
ipcMain.on('gapps-get-visibility', (event) => {
  const tab = findTabBySender(event.sender);
  event.returnValue = tab ? computeTabVisible(tab.id) : true;
});

// Receive notifications from web pages (Gmail, Google Chat, etc.)
function isTrustedIpcSender(event) {
  try {
    const url = (event.senderFrame && event.senderFrame.url) || event.sender.getURL();
    return isTrustedOrigin(url);
  } catch (_) {
    return false;
  }
}

function clampString(value, max) {
  return typeof value === 'string' ? value.slice(0, max) : '';
}

ipcMain.on('tab-notification', (event, data) => {
  // Only real Google pages may raise desktop notifications (prevents spoofed
  // "Gmail • ..." popups from user-hosted or third-party content)
  if (!isTrustedIpcSender(event)) return;
  const raw = data || {};
  const id = clampString(raw.id, 64);
  const title = clampString(raw.title, 200);
  const body = clampString(raw.body, 1000);
  // data:image icons can be large; truncating them would just corrupt the image
  const icon =
    typeof raw.icon === 'string' && raw.icon.startsWith('data:image/')
      ? (raw.icon.length <= 512 * 1024 ? raw.icon : '')
      : clampString(raw.icon, 2048);
  const tag = clampString(raw.tag, 200);
  const silent = Boolean(raw.silent);
  const senderTab = findTabBySender(event.sender);

  let appId = senderTab ? senderTab.app : null;
  if (!appId) {
    const url = event.sender.getURL();
    if (url.includes('chat.google.com') || url.includes('mail.google.com/chat')) {
      appId = 'chat';
    } else if (url.includes('mail.google.com')) {
      appId = 'gmail';
    } else if (url.includes('calendar.google.com')) {
      appId = 'calendar';
    } else if (url.includes('meet.google.com')) {
      appId = 'meet';
    } else if (url.includes('gemini.google.com')) {
      appId = 'gemini';
    } else {
      const detected = detectApp(url);
      appId = detected ? detected.id : 'gmail';
    }
  }

  const targetTab = senderTab || state.tabs.find((t) => t.app === appId);
  if (targetTab) {
    targetTab.lastNativeNotificationAt = Date.now();
  }

  // If user is currently actively viewing this exact tab in the focused foreground window,
  // we don't display a desktop notification toast popup
  const activelyViewed = Boolean(targetTab && isTabActivelyViewed(targetTab.id));
  if (activelyViewed) return;

  // Unread counts come only from the tab's unread observer (tab-unread-count).
  // Here we only flag the tab, so apps without a counter (e.g. Calendar) still get a dot.
  if (targetTab && !targetTab.hasNotification) {
    targetTab.hasNotification = true;
    updateAppBadge();
    broadcastState();
  }

  showCustomNotification({
    title,
    body,
    icon,
    tag,
    silent,
    appId,
    tabId: targetTab ? targetTab.id : null,
    pageNotificationId: id || null,
    sourceWebContents: event.sender
  });
});

// User activity in tab
ipcMain.on('tab-user-active', () => {
  // We do NOT clear unread counts on mere clicks or keypresses.
  // The tab's unread badges are cleared only when the web app itself reduces unread count to 0.
});

// Fallback desktop notification when an unread counter increases but the web app
// did not raise its own notification (e.g. Gmail desktop notifications disabled).
const FALLBACK_NOTIFICATION_DELAY_MS = 4000;
const NATIVE_NOTIFICATION_WINDOW_MS = 10000;

function scheduleFallbackNotification(tabId, prevCount) {
  const tab = state.tabs.find((t) => t.id === tabId);
  if (!tab) return;
  const increasedAt = Date.now();
  if (tab.fallbackNotificationTimer) clearTimeout(tab.fallbackNotificationTimer);
  tab.fallbackNotificationTimer = setTimeout(() => {
    const t = state.tabs.find((x) => x.id === tabId);
    if (!t) return;
    t.fallbackNotificationTimer = null;
    if (t.lastNativeNotificationAt && t.lastNativeNotificationAt > increasedAt - NATIVE_NOTIFICATION_WINDOW_MS) return;
    if (isTabActivelyViewed(tabId)) return;
    const current = t.unreadCount || 0;
    if (current <= prevCount) return;
    const appDef = byId(t.app);
    const appName = appDef ? appDef.title : 'Google Suite';
    showCustomNotification({
      title: '',
      body: current === 1 ? `1 messaggio non letto in ${appName}` : `${current} messaggi non letti in ${appName}`,
      tag: 'gapps-unread-summary',
      appId: t.app,
      tabId: t.id
    });
  }, FALLBACK_NOTIFICATION_DELAY_MS);
}

// Unread badge reporting from tab DOM observer: single source of truth for unread counts
ipcMain.on('tab-unread-count', (event, data) => {
  if (!isTrustedIpcSender(event)) return;
  const senderTab = findTabBySender(event.sender);
  if (!senderTab) return;

  const { count } = data || {};
  const prevCount = senderTab.unreadCount || 0;
  const num = Math.min(99999, Math.max(0, typeof count === 'number' ? Math.floor(count) || 0 : parseInt(count, 10) || 0));

  if (num === 0) {
    if (senderTab.unreadCount > 0 || senderTab.hasNotification) {
      senderTab.unreadCount = 0;
      senderTab.hasNotification = false;
      updateAppBadge();
      broadcastState();
    }
    return;
  }

  if (num === prevCount) return;

  senderTab.unreadCount = num;
  updateAppBadge();
  broadcastState();

  if (num > prevCount && !isTabActivelyViewed(senderTab.id)) {
    scheduleFallbackNotification(senderTab.id, prevCount);
  }
});

app.on('second-instance', (_event, commandLine) => {
  if (mainWindow) {
    if (mainWindow.isMinimized()) mainWindow.restore();
    mainWindow.show();
    mainWindow.focus();
  }
  handleArgv(commandLine.slice(1));
});

// Defense in depth for every webContents (including ones created later):
// no <webview> embedding, no popups unless a view installs its own handler.
app.on('web-contents-created', (_event, contents) => {
  contents.on('will-attach-webview', (e) => e.preventDefault());
  contents.setWindowOpenHandler(() => ({ action: 'deny' }));
});

app.whenReady().then(async () => {
  app.setName('Google Suite');
  if (app.setDesktopName) {
    app.setDesktopName('google-suite.desktop');
  }
  app.setAppUserModelId('com.google.suite.linux');
  ensureDesktopFile();
  loadSettings();
  loadState();

  // Register Global System Hotkey (Ctrl+Alt+G) to toggle Google Suite from anywhere on Linux
  try {
    globalShortcut.register('CommandOrControl+Alt+G', () => {
      toggleWindow();
    });
  } catch (err) {
    console.warn('Could not register global hotkey:', err);
  }

  // Strip Electron and app identifiers from User-Agent so Google accounts & services don't block login
  const defaultUa = session.defaultSession.getUserAgent();
  const cleanUa = defaultUa
    .replace(/Electron\/\S+\s?/, '')
    .replace(/google-suite-linux\/\S+\s?/, '')
    .replace(/google-suite\/\S+\s?/, '')
    .replace(/GoogleSuite\/\S+\s?/, '')
    .replace(/gapps\/\S+\s?/, '')
    .trim();
  session.defaultSession.setUserAgent(cleanUa, 'en-US,en;q=0.9');

  // Default to English language for Google Workspace web services
  session.defaultSession.webRequest.onBeforeSendHeaders((details, callback) => {
    const headers = { ...details.requestHeaders };
    if (!headers['Accept-Language']) {
      headers['Accept-Language'] = 'en-US,en;q=0.9';
    }
    callback({ requestHeaders: headers });
  });

  // Permissions: grant only a whitelist, and only to trusted Google origins
  // (https://*.google.com). Third-party iframes (ads, embeds in Docs/Gmail) and
  // user-hosted content (*.googleusercontent.com) get nothing.
  session.defaultSession.setPermissionCheckHandler((_webContents, permission, requestingOrigin) => {
    return isPermissionAllowed(permission, requestingOrigin);
  });

  session.defaultSession.setPermissionRequestHandler((webContents, permission, callback, details) => {
    const origin =
      (details && (details.requestingUrl || details.securityOrigin)) ||
      (webContents && !webContents.isDestroyed() ? webContents.getURL() : '');
    const allowed = isPermissionAllowed(permission, origin);
    if (!allowed) {
      console.warn(`[Google Suite] Denied permission "${permission}" for ${String(origin).slice(0, 120)}`);
    }
    callback(allowed);
  });

  // Screen sharing (Google Meet): only for trusted origins, and always let the user
  // choose what to share. On Wayland the PipeWire portal already shows its own picker.
  if (session.defaultSession.setDisplayMediaRequestHandler) {
    session.defaultSession.setDisplayMediaRequestHandler((request, callback) => {
      const origin =
        (request && (request.securityOrigin || (request.frame && request.frame.url))) || '';
      if (!isTrustedOrigin(origin)) {
        console.warn(`[Google Suite] Denied screen capture for ${String(origin).slice(0, 120)}`);
        callback({});
        return;
      }
      // Do NOT pass thumbnailSize {0,0}: on Wayland/PipeWire (Electron 33) it makes the
      // main process SIGSEGV right after the user picks a source in the portal dialog.
      desktopCapturer
        .getSources({ types: ['screen', 'window'] })
        .then((sources) => pickDisplaySource(sources))
        .then((source) => callback(source ? { video: source } : {}))
        .catch(() => callback({}));
    });
  }

  // Determine target window bounds on the current monitor (where cursor is located)
  const defaultWidth = 1280;
  const defaultHeight = 860;
  let targetBounds = null;

  try {
    const cursorPoint = screen.getCursorScreenPoint();
    const currentDisplay = screen.getDisplayNearestPoint(cursorPoint);
    if (currentDisplay && currentDisplay.workArea) {
      const area = currentDisplay.workArea;
      if (settings.window_bounds && typeof settings.window_bounds === 'object') {
        const wb = settings.window_bounds;
        // Verify saved bounds are on a connected display
        const displays = screen.getAllDisplays();
        const onAnyDisplay = displays.some((d) => {
          const da = d.bounds;
          return (
            wb.x >= da.x - 50 &&
            wb.x < da.x + da.width &&
            wb.y >= da.y - 50 &&
            wb.y < da.y + da.height
          );
        });
        if (onAnyDisplay) {
          targetBounds = wb;
        }
      }

      if (!targetBounds) {
        const w = Math.min(defaultWidth, area.width - 40);
        const h = Math.min(defaultHeight, area.height - 40);
        const x = area.x + Math.max(0, Math.round((area.width - w) / 2));
        const y = area.y + Math.max(0, Math.round((area.height - h) / 2));
        targetBounds = { x, y, width: w, height: h };
      }
    }
  } catch (err) {
    console.warn('Could not determine current display position:', err);
  }

  // Create main window
  const appWindowIcon = nativeImage.createFromPath(ICON_PATH);
  const windowOpts = {
    width: (targetBounds && targetBounds.width) || defaultWidth,
    height: (targetBounds && targetBounds.height) || defaultHeight,
    minWidth: 700,
    minHeight: 500,
    title: 'Google Suite',
    icon: appWindowIcon,
    autoHideMenuBar: true,
    backgroundColor: '#202124',
    show: false
  };

  if (targetBounds && targetBounds.x !== undefined && targetBounds.y !== undefined) {
    windowOpts.x = targetBounds.x;
    windowOpts.y = targetBounds.y;
  }

  mainWindow = new BrowserWindow(windowOpts);
  try {
    mainWindow.setIcon(appWindowIcon);
  } catch (_) {}

  // Setup default application edit menu so system copy/paste shortcuts route properly
  const appMenuTemplate = [
    {
      label: 'Edit',
      submenu: [
        { role: 'undo' },
        { role: 'redo' },
        { type: 'separator' },
        { role: 'cut' },
        { role: 'copy' },
        { role: 'paste' },
        { role: 'pasteAndMatchStyle' },
        { role: 'selectAll' }
      ]
    }
  ];
  Menu.setApplicationMenu(Menu.buildFromTemplate(appMenuTemplate));

  // Create permanent 36px tab bar view at top
  tabbarView = new WebContentsView({
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      contextIsolation: true,
      nodeIntegration: false,
      sandbox: true,
      backgroundThrottling: false
    }
  });

  tabbarView.webContents.loadFile(path.join(__dirname, 'tabbar', 'index.html'));
  mainWindow.contentView.addChildView(tabbarView);

  // Attach active tab immediately for instant startup
  if (state.active) {
    activateTab(state.active);
  }

  // Preload all background tabs (Chat, Gmail, Calendar, etc.) so real-time notifications
  // and WebSockets are connected immediately at launch without needing manual clicks!
  setTimeout(() => {
    state.tabs.forEach((tab) => {
      if (tab.id !== state.active && !tabViews.has(tab.id) && !tab.url.startsWith('file://')) {
        try {
          const view = createTabView(tab);
          tabViews.set(tab.id, view);
        } catch (err) {
          console.error(`Failed to preload background tab ${tab.app}:`, err);
        }
      }
    });
  }, 1000);

  // Safely ensure app icons in the background without blocking window launch
  setTimeout(() => {
    ensureAppIcons().catch((err) => console.warn('Background icon verification:', err));
  }, 2000);

  updateBounds();

  let saveBoundsTimer = null;
  const rememberBounds = () => {
    scheduleUpdateBounds();
    if (!mainWindow || mainWindow.isDestroyed() || mainWindow.isMaximized() || mainWindow.isFullScreen()) {
      return;
    }
    clearTimeout(saveBoundsTimer);
    saveBoundsTimer = setTimeout(() => {
      try {
        if (mainWindow && !mainWindow.isDestroyed() && !mainWindow.isMaximized() && !mainWindow.isFullScreen()) {
          settings.window_bounds = mainWindow.getBounds();
          saveSettings();
        }
      } catch (_) {}
    }, 400);
  };

  mainWindow.on('resize', rememberBounds);
  mainWindow.on('resized', rememberBounds);
  mainWindow.on('move', rememberBounds);
  mainWindow.on('moved', rememberBounds);
  mainWindow.on('maximize', scheduleUpdateBounds);
  mainWindow.on('unmaximize', scheduleUpdateBounds);
  mainWindow.on('enter-full-screen', scheduleUpdateBounds);
  mainWindow.on('leave-full-screen', scheduleUpdateBounds);
  mainWindow.on('restore', scheduleUpdateBounds);

  // Close to tray / quit behavior
  mainWindow.on('close', (event) => {
    saveStateSync();
    if (!app.isQuitting) {
      if (settings.close_action === 'quit') {
        app.isQuitting = true;
        app.quit();
        return;
      }
      event.preventDefault();
      mainWindow.hide();
    }
  });

  mainWindow.on('show', updateTrayMenu);
  mainWindow.on('hide', updateTrayMenu);

  // Keep tab page visibility (document.hidden) in sync with the real window state
  ['show', 'hide', 'minimize', 'restore', 'focus', 'blur'].forEach((evt) => {
    mainWindow.on(evt, () => syncTabVisibility());
  });

  createTray();

  // Show window: always show if on GNOME or testing, or if not started minimized
  const isGnome = getEffectiveTheme() === 'gnome';
  if (!settings.start_minimized || isGnome || allowMultiple || process.argv.includes('--show')) {
    mainWindow.show();
    mainWindow.focus();
  }

  console.log(`[Google Suite] App ready (Theme: ${getEffectiveTheme().toUpperCase()} | Window visible: ${mainWindow.isVisible()})`);
  if (isGnome) {
    console.log(`[Google Suite] GNOME Note: GNOME Shell does not display tray icons by default.`);
  }

  // Handle CLI args
  handleArgv(process.argv.slice(1));

  // Check for new releases on startup (after 4 seconds to allow initial page to load smoothly)
  setTimeout(() => {
    checkForAppUpdates(false);
  }, 4000);
});

app.on('activate', () => {
  if (mainWindow) {
    mainWindow.show();
    mainWindow.focus();
  }
});

app.on('will-quit', () => {
  globalShortcut.unregisterAll();
});

app.on('before-quit', () => {
  saveStateSync();
  app.isQuitting = true;
});
