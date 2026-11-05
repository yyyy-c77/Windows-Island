using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Management;
using System.Net.Http;
using System.Net.NetworkInformation;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Interop;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Media.Imaging;
using System.Windows.Threading;
using AudioSwitcher.AudioApi.CoreAudio;
using Microsoft.Win32;
using NAudio.Wave;
using Windows.Devices.Enumeration;
using Windows.Devices.Radios;
using Windows.Devices.Bluetooth;
using Windows.Devices.WiFi;
using Windows.Devices.Power;
using Windows.Media.Control;
using Windows.UI.Notifications;
using Windows.UI.Notifications.Management;
using Windows.Storage.Streams;
using WinForms = System.Windows.Forms;
using Drawing = System.Drawing;
using Rectangle = System.Windows.Shapes.Rectangle;

namespace Island;

public class WeatherInfo
{
    public double CurrentTemp { get; set; } = 18;
    public int CurrentCode { get; set; } = 0;
    public double Humidity { get; set; } = 45;
    public double WindSpeed { get; set; } = 3;
    public List<DailyWeather> Daily { get; set; } = new List<DailyWeather>();
}

public class DailyWeather
{
    public string Date { get; set; } = "";
    public int Code { get; set; } = 0;
    public double MaxTemp { get; set; } = 20;
    public double MinTemp { get; set; } = 10;
}

public partial class MainWindow : Window
{
    private static double L1W = 280;
    private static double L2W = 520;
    private static double L3H = 400;
    private static double TopMargin = 8;

    private const int GWL_EXSTYLE = -20;
    private const int WS_EX_TOOLWINDOW = 0x00000080;

    [DllImport("user32.dll")] private static extern int GetWindowLong(IntPtr hWnd, int nIndex);
    [DllImport("user32.dll")] private static extern int SetWindowLong(IntPtr hWnd, int nIndex, int dwNewLong);
    [DllImport("user32.dll", CharSet = CharSet.Auto)] private static extern bool DestroyIcon(IntPtr handle);
    [DllImport("user32.dll", SetLastError = true)] private static extern bool AddClipboardFormatListener(IntPtr hwnd);
    [DllImport("user32.dll", SetLastError = true)] private static extern bool RemoveClipboardFormatListener(IntPtr hwnd);
    [DllImport("shell32.dll")] private static extern int SHEmptyRecycleBin(IntPtr hwnd, string pszRootPath, uint dwFlags);

    [DllImport("user32.dll")] private static extern IntPtr GetForegroundWindow();
    [DllImport("user32.dll")] private static extern bool GetWindowRect(IntPtr hWnd, out RECT lpRect);
    [DllImport("user32.dll")] private static extern IntPtr MonitorFromWindow(IntPtr hwnd, uint dwFlags);
    [DllImport("user32.dll")] private static extern bool GetMonitorInfo(IntPtr hMonitor, ref MONITORINFO lpmi);
    [DllImport("user32.dll")] private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint processId);

    [DllImport("shell32.dll")]
    private static extern int SHQueryUserNotificationState(out QUERY_USER_NOTIFICATION_STATE pquns);

    public enum QUERY_USER_NOTIFICATION_STATE
    {
        QUNS_NOT_PRESENT = 1, QUNS_BUSY = 2, QUNS_RUNNING_D3D_FULL_SCREEN = 3,
        QUNS_PRESENTATION_MODE = 4, QUNS_ACCEPTS_NOTIFICATIONS = 5, QUNS_QUIET_TIME = 6, QUNS_APP = 7
    }

    [StructLayout(LayoutKind.Sequential)] public struct RECT { public int Left, Top, Right, Bottom; }
    [StructLayout(LayoutKind.Sequential)] public struct MONITORINFO { public int cbSize; public RECT rcMonitor; public RECT rcWork; public uint dwFlags; }

    private const int WM_CLIPBOARDUPDATE = 0x031D;

    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Auto)]
    private struct SHFILEINFO
    {
        public IntPtr hIcon;
        public int iIcon;
        public uint dwAttributes;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)] public string szDisplayName;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 80)] public string szTypeName;
    }

    [DllImport("shell32.dll", CharSet = CharSet.Auto)]
    private static extern IntPtr SHGetFileInfo(string pszPath, uint dwFileAttributes, out SHFILEINFO psfi, uint cbFileInfo, uint uFlags);

    private const uint SHGFI_ICON = 0x000000100;
    private const uint SHGFI_LARGEICON = 0x000000000;

    private delegate bool EnumWindowsProc(IntPtr hWnd, IntPtr lParam);
    [DllImport("user32.dll")] private static extern bool EnumWindows(EnumWindowsProc enumProc, IntPtr lParam);
    [DllImport("user32.dll")] private static extern bool IsWindowVisible(IntPtr hWnd);
    [DllImport("user32.dll")] private static extern int GetWindowText(IntPtr hWnd, StringBuilder text, int count);
    [DllImport("user32.dll")] private static extern bool SetForegroundWindow(IntPtr hWnd);
    [DllImport("user32.dll")] private static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);
    [DllImport("user32.dll")] private static extern IntPtr GetWindow(IntPtr hWnd, uint uCmd);
    [DllImport("user32.dll")] private static extern IntPtr SendMessage(IntPtr hWnd, int Msg, IntPtr wParam, IntPtr lParam);
    [DllImport("user32.dll", EntryPoint = "GetClassLongPtr")] private static extern IntPtr GetClassLongPtr64(IntPtr hWnd, int nIndex);
    [DllImport("user32.dll", EntryPoint = "GetClassLong")] private static extern IntPtr GetClassLongPtr32(IntPtr hWnd, int nIndex);

    private const int WM_GETICON = 0x007F;
    private const int ICON_SMALL2 = 2;
    private const int GCLP_HICONSM = -34;
    private const uint GW_OWNER = 4;
    private const int SW_RESTORE = 9;

    private enum State { L1, L2, L3 }

    private State _state = State.L1;
    private string _currentPanelKey = "";
    private int _panelGeneration = 0;
    private readonly DispatcherTimer _closeTimer;
    private readonly DispatcherTimer _leaveL2Timer;
    private readonly DispatcherTimer _clockTimer;
    private readonly DispatcherTimer _windowWatcherTimer;
    private readonly DispatcherTimer _mediaWatcherTimer;
    private readonly DispatcherTimer _lyricTimer;
    private readonly DispatcherTimer _notificationTimer;
    private readonly DispatcherTimer _pomoTimer;
    private readonly DispatcherTimer _sysMonitorTimer;
    private readonly DispatcherTimer _volumeTimer;

    private readonly Border[] _windowIcons = new Border[5];
    private readonly Image[] _windowImages = new Image[5];
    private List<(string Name, string Path, IntPtr Hwnd)> _taskbarApps = new();
    private Dictionary<string, int> _appLaunchCounts = new Dictionary<string, int>();
    private string _statsFilePath = "";

    private readonly SolidColorBrush ColorTextPrimary = new SolidColorBrush(Color.FromRgb(255, 255, 255));
    private readonly SolidColorBrush ColorTextSecondary = new SolidColorBrush(Color.FromArgb(153, 255, 255, 255));
    private readonly SolidColorBrush ColorCardBg = new SolidColorBrush(Color.FromArgb(30, 255, 255, 255));
    private readonly SolidColorBrush ColorHoverBg = new SolidColorBrush(Color.FromArgb(50, 255, 255, 255));
    private readonly SolidColorBrush ColorAccent = new SolidColorBrush(Color.FromRgb(52, 199, 89));
    private readonly SolidColorBrush ColorRed = new SolidColorBrush(Color.FromRgb(255, 59, 48));

    private GlobalSystemMediaTransportControlsSessionManager? _mediaManager;
    private GlobalSystemMediaTransportControlsSession? _currentSession;
    private bool _isMediaPlaying = false;

    private string _currentSongName = "";
    private string _currentTitle = "";
    private string _currentArtist = "";
    private BitmapImage? _currentAlbumArt = null;
    private string _currentRequestSong = "";

    private double _mTime = 45, _mWeather = 35, _mWifi = 25, _mNetSpeed = 38;
    private double _mSettings = 22, _mBt = 22, _mNotif = 35, _mMedia = 22, _mStart = 22;

    private List<(TimeSpan Time, string Text)> _lyrics = new();
    private StackPanel _lyricStack = new();
    private int _currentLyricIndex = -1;
    private TextBlock? _titleTextBlock;
    private TextBlock? _artistTextBlock;
    private ProgressBar? _currentProgressBar;

    private TimeSpan _basePosition = TimeSpan.Zero;
    private DateTime _baseTime = DateTime.MinValue;
    private bool _isSystemPlaying = false;

    private string _customLocation = "天津市 津南区";
    private WeatherInfo _currentWeather = new WeatherInfo();

    private List<string> _clipboardHistory = new();
    private IntPtr _hwnd;
    private bool _isNotificationShowing = false;
    private bool _isPomoRunning = false;
    private DateTime _pomoEndTime;
    private WinForms.NotifyIcon? _notifyIcon;
    private static readonly CoreAudioController AudioController = new CoreAudioController();

    private long _lastBytesSent = 0, _lastBytesReceived = 0;
    private bool _isFullScreen = false;
    private double _currentVolume = 0;

    private Border _netSpeedBox = new Border { Height = 24, VerticalAlignment = VerticalAlignment.Center };
    private TextBlock _netSpeedText = new TextBlock { Foreground = new SolidColorBrush(Color.FromRgb(255, 255, 255)), FontFamily = new FontFamily("Bahnschrift"), VerticalAlignment = VerticalAlignment.Center, TextAlignment = TextAlignment.Left, FontSize = 12 };

    private WasapiLoopbackCapture? _loopbackCapture;
    private Canvas _visualizerCanvas = new Canvas { Height = 40 };
    private double[] _fftData = new double[16];
    private double _currentAudioPower = 0;

    private bool _isStartupEnabled;
    private bool _isFullScreenHideEnabled = true;
    private bool _isNotificationInterruptEnabled = true;

    private double GetL1H() => _isMediaPlaying ? 54 : 32;
    private double GetL2H() => _isMediaPlaying ? 54 : 40;

    public MainWindow()
    {
        InitializeComponent();
        BuildWindowIcons();
        LoadConfig();
        InitTrayIcon();
        InitAudioVisualizer();
        SetWindowIcon();

        _netSpeedBox.Child = _netSpeedText;
        Stage.Children.Add(_netSpeedBox);

        _statsFilePath = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), @"IslandWidget\app_stats.json");
        LoadStats();
        _isStartupEnabled = CheckStartup();

        Loaded += async (_, _) => {
            MeasureStaticElements();
            Relayout();
            UpdateClock();
            await RequestWinRTPermissions();
            await InitMediaManager();
            InitNotifications();
            FetchWeatherDataAsync();
        };

        SizeChanged += (_, _) => Relayout();
        MouseEnter += (s, e) => OnMouseEnter();
        MouseLeave += (s, e) => OnMouseLeave();

        _closeTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _closeTimer.Tick += (_, _) => { _closeTimer.Stop(); GoL1(); };

        _leaveL2Timer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _leaveL2Timer.Tick += (_, _) => { _leaveL2Timer.Stop(); GoL1(); };

        _clockTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _clockTimer.Tick += (_, _) => UpdateClock();
        _clockTimer.Start();

        _windowWatcherTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _windowWatcherTimer.Tick += (_, _) => UpdateActiveWindows();
        _windowWatcherTimer.Start();

        _mediaWatcherTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(2) };
        _mediaWatcherTimer.Tick += async (_, _) => await CheckMediaStatus();
        _mediaWatcherTimer.Start();

        _lyricTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(100) };
        _lyricTimer.Tick += (_, _) => UpdateLyricScroll();
        _lyricTimer.Start();

        _notificationTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(3) };
        _notificationTimer.Tick += (_, _) => { _notificationTimer.Stop(); _isNotificationShowing = false; Relayout(); };

        _pomoTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _pomoTimer.Tick += (_, _) => UpdatePomodoro();

        _sysMonitorTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
        _sysMonitorTimer.Tick += (_, _) => UpdateSystemStatus();
        _sysMonitorTimer.Start();

        _volumeTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(500) };
        _volumeTimer.Tick += (_, _) => CheckVolumeChange();
        _volumeTimer.Start();

        WeatherText.MouseLeftButtonDown += (_, _) => OpenPanel("天气");
        SettingsIcon.MouseLeftButtonDown += (_, _) => OpenPanel("设置");
        WifiIcon.MouseLeftButtonDown += (_, _) => OpenPanel("WiFi");
        BtIcon.MouseLeftButtonDown += (_, _) => OpenPanel("蓝牙");
        NotificationBox.MouseLeftButtonDown += (_, _) => OpenPanel("通知");
        MediaBox.MouseLeftButtonDown += (_, _) => OpenPanel("音乐");
        LyricBox.MouseLeftButtonDown += (_, _) => OpenPanel("音乐");
        StartBox.MouseLeftButtonDown += (_, _) => OpenPanel("控制中心");
    }

    private void SetStartup(bool enable)
    {
        try
        {
            string exePath = Environment.ProcessPath ?? "";
            if (string.IsNullOrEmpty(exePath)) return;
            using var key = Registry.CurrentUser.OpenSubKey(@"Software\Microsoft\Windows\CurrentVersion\Run", true);
            if (enable) key?.SetValue("IslandWidget", $"\"{exePath}\"");
            else key?.DeleteValue("IslandWidget", false);
        }
        catch { }
    }

    private bool CheckStartup()
    {
        try
        {
            using var key = Registry.CurrentUser.OpenSubKey(@"Software\Microsoft\Windows\CurrentVersion\Run", false);
            return key?.GetValue("IslandWidget") != null;
        }
        catch { return false; }
    }

    private void LoadStats()
    {
        try
        {
            if (File.Exists(_statsFilePath))
            {
                string json = File.ReadAllText(_statsFilePath);
                _appLaunchCounts = JsonSerializer.Deserialize<Dictionary<string, int>>(json) ?? new Dictionary<string, int>();
            }
        }
        catch { _appLaunchCounts = new Dictionary<string, int>(); }
    }

    private void SaveStats()
    {
        try
        {
            string dir = System.IO.Path.GetDirectoryName(_statsFilePath)!;
            if (!Directory.Exists(dir)) Directory.CreateDirectory(dir);
            string json = JsonSerializer.Serialize(_appLaunchCounts);
            File.WriteAllText(_statsFilePath, json);
        }
        catch { }
    }

    private void FetchWeatherDataAsync()
    {
        _ = Task.Run(async () =>
        {
            try
            {
                using var client = new HttpClient { Timeout = TimeSpan.FromSeconds(5) };
                var geoUrl = $"https://geocoding-api.open-meteo.com/v1/search?name={Uri.EscapeDataString(_customLocation)}&count=1&language=zh&format=json";
                var geoJson = await client.GetStringAsync(geoUrl);
                using var geoDoc = JsonDocument.Parse(geoJson);

                double lat = 39.08, lon = 117.20;
                if (geoDoc.RootElement.TryGetProperty("results", out var results) && results.GetArrayLength() > 0)
                {
                    lat = results[0].GetProperty("latitude").GetDouble();
                    lon = results[0].GetProperty("longitude").GetDouble();
                }
                else
                {
                    geoUrl = $"https://geocoding-api.open-meteo.com/v1/search?name={Uri.EscapeDataString(_customLocation.Replace(" ", ""))}&count=1&language=zh&format=json";
                    geoJson = await client.GetStringAsync(geoUrl);
                    using var geoDoc2 = JsonDocument.Parse(geoJson);
                    if (geoDoc2.RootElement.TryGetProperty("results", out var results2) && results2.GetArrayLength() > 0)
                    {
                        lat = results2[0].GetProperty("latitude").GetDouble();
                        lon = results2[0].GetProperty("longitude").GetDouble();
                    }
                }

                var weatherUrl = $"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}&current=temperature_2m,relative_humidity_2m,weather_code,wind_speed_10m&daily=weather_code,temperature_2m_max,temperature_2m_min&timezone=auto";
                var weatherJson = await client.GetStringAsync(weatherUrl);
                using var weatherDoc = JsonDocument.Parse(weatherJson);
                var root = weatherDoc.RootElement;

                _currentWeather.CurrentTemp = Math.Round(root.GetProperty("current").GetProperty("temperature_2m").GetDouble());
                _currentWeather.CurrentCode = root.GetProperty("current").GetProperty("weather_code").GetInt32();
                _currentWeather.Humidity = root.GetProperty("current").GetProperty("relative_humidity_2m").GetDouble();
                _currentWeather.WindSpeed = root.GetProperty("current").GetProperty("wind_speed_10m").GetDouble();

                _currentWeather.Daily.Clear();
                var daily = root.GetProperty("daily");
                var times = daily.GetProperty("time");
                var codes = daily.GetProperty("weather_code");
                var maxTemps = daily.GetProperty("temperature_2m_max");
                var minTemps = daily.GetProperty("temperature_2m_min");

                for (int i = 0; i < times.GetArrayLength(); i++)
                {
                    _currentWeather.Daily.Add(new DailyWeather
                    {
                        Date = times[i].GetString() ?? "",
                        Code = codes[i].GetInt32(),
                        MaxTemp = Math.Round(maxTemps[i].GetDouble()),
                        MinTemp = Math.Round(minTemps[i].GetDouble())
                    });
                }

                Dispatcher.Invoke(() =>
                {
                    WeatherText.Text = $"{_currentWeather.CurrentTemp}°";
                    MeasureStaticElements();
                    Relayout();
                    if (_state == State.L3 && _currentPanelKey == "天气") LoadWeatherPanel();
                });
            }
            catch { }
        });
    }

    private string GetWeatherDesc(int code)
    {
        return code switch
        {
            0 => "晴",
            1 or 2 or 3 => "多云",
            45 or 48 => "雾",
            51 or 53 or 55 => "毛毛雨",
            61 or 63 or 65 => "雨",
            71 or 73 or 75 => "雪",
            80 or 81 or 82 => "阵雨",
            95 or 96 or 99 => "雷阵雨",
            _ => "阴"
        };
    }

    private string FormatDate(string dateStr, int index)
    {
        if (index == 0) return "今天";
        if (index == 1) return "明天";
        try
        {
            var date = DateTime.Parse(dateStr);
            string dayStr = date.DayOfWeek switch
            {
                DayOfWeek.Monday => "一",
                DayOfWeek.Tuesday => "二",
                DayOfWeek.Wednesday => "三",
                DayOfWeek.Thursday => "四",
                DayOfWeek.Friday => "五",
                DayOfWeek.Saturday => "六",
                _ => "日"
            };
            return "周" + dayStr;
        }
        catch { return dateStr; }
    }

    private void SetWindowIcon()
    {
        try
        {
            string exePath = Environment.ProcessPath ?? "";
            if (!string.IsNullOrEmpty(exePath) && File.Exists(exePath))
            {
                using var icon = Drawing.Icon.ExtractAssociatedIcon(exePath);
                if (icon != null) this.Icon = Imaging.CreateBitmapSourceFromHIcon(icon.Handle, Int32Rect.Empty, BitmapSizeOptions.FromEmptyOptions());
            }
        }
        catch { }
    }

    private void SetupTextBox(TextBox tb, Action<string> onSave)
    {
        tb.GotFocus += (s, e) => { this.Activate(); };
        tb.KeyDown += (s, e) => { if (e.Key == Key.Enter) { onSave(tb.Text.Trim()); Keyboard.ClearFocus(); } };
        tb.LostFocus += (s, e) => { onSave(tb.Text.Trim()); };
    }

    private void InitAudioVisualizer()
    {
        try
        {
            _loopbackCapture = new WasapiLoopbackCapture();
            _loopbackCapture.DataAvailable += (s, a) =>
            {
                var buffer = new WaveBuffer(a.Buffer);
                int samples = a.BytesRecorded / 4;
                if (samples <= 0) return;

                double sum = 0;
                for (int i = 0; i < samples; i += 10) sum += Math.Abs(buffer.FloatBuffer[i]);

                Dispatcher.Invoke(() =>
                {
                    _currentAudioPower = Math.Min(1.0, (sum / (samples / 10 + 1)) * 5);
                    if (_currentAudioPower < 0.01) _currentAudioPower = 0;

                    var rnd = new Random();
                    for (int i = 0; i < _fftData.Length; i++) _fftData[i] = _currentAudioPower * (rnd.NextDouble() * 0.8 + 0.2);
                    DrawVisualizer();
                });
            };
            _loopbackCapture.StartRecording();
        }
        catch { }
    }

    private void DrawVisualizer()
    {
        if (_visualizerCanvas.Children.Count == 0) return;
        for (int i = 0; i < _fftData.Length; i++)
        {
            if (_visualizerCanvas.Children[i] is Rectangle rect)
            {
                double val = _fftData[i] * 40;
                rect.Height = Math.Clamp(val, 2, 40);
                Canvas.SetTop(rect, 40 - rect.Height);
            }
        }
    }

    private void UpdateActiveWindows()
    {
        var runningWindows = new List<(string Name, string Path, IntPtr Hwnd)>();

        IntPtr myHwnd = new WindowInteropHelper(this).Handle;
        EnumWindows((hWnd, lParam) =>
        {
            if (hWnd == myHwnd || !IsWindowVisible(hWnd) || GetWindow(hWnd, GW_OWNER) != IntPtr.Zero) return true;
            int exStyle = GetWindowLong(hWnd, GWL_EXSTYLE);
            if ((exStyle & WS_EX_TOOLWINDOW) != 0) return true;

            var sb = new StringBuilder(256);
            GetWindowText(hWnd, sb, 256);
            if (sb.Length == 0) return true;

            try
            {
                uint pid;
                GetWindowThreadProcessId(hWnd, out pid);
                var proc = Process.GetProcessById((int)pid);
                string processName = proc.ProcessName.ToLower();

                if (processName == "explorer" || processName == "textinputhost" || processName == "searchapp") return true;

                string path = proc.MainModule?.FileName ?? "";
                string name = proc.ProcessName;

                if (!runningWindows.Any(x => x.Name == name))
                    runningWindows.Add((name, path, hWnd));
            }
            catch { }

            return true;
        }, IntPtr.Zero);

        var sortedWindows = runningWindows
            .OrderByDescending(x => _appLaunchCounts.ContainsKey(x.Name) ? _appLaunchCounts[x.Name] : 0)
            .ToList();

        if (sortedWindows.Count < 5)
        {
            string pinnedPath = System.IO.Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), @"Microsoft\Internet Explorer\Quick Launch\User Pinned\TaskBar");
            if (Directory.Exists(pinnedPath))
            {
                var pinnedApps = Directory.GetFiles(pinnedPath, "*.lnk").Select(f => new {
                    Name = System.IO.Path.GetFileNameWithoutExtension(f),
                    Path = f
                })
                .OrderByDescending(x => _appLaunchCounts.ContainsKey(x.Name) ? _appLaunchCounts[x.Name] : 0);

                foreach (var pApp in pinnedApps)
                {
                    if (!sortedWindows.Any(x => x.Name.Equals(pApp.Name, StringComparison.OrdinalIgnoreCase)))
                        sortedWindows.Add((pApp.Name, pApp.Path, IntPtr.Zero));
                    if (sortedWindows.Count >= 5) break;
                }
            }
        }

        _taskbarApps = sortedWindows.Take(5).ToList();

        for (int i = 0; i < 5; i++)
        {
            if (i < _taskbarApps.Count)
            {
                var app = _taskbarApps[i];
                _windowImages[i].Source = app.Hwnd != IntPtr.Zero ? GetWindowIcon(app.Hwnd) : GetFileIcon(app.Path);
                _windowIcons[i].Visibility = Visibility.Visible;
            }
            else
            {
                _windowIcons[i].Visibility = Visibility.Collapsed;
            }
        }
    }

    private void FocusWindow(int index)
    {
        if (index >= _taskbarApps.Count) return;
        var app = _taskbarApps[index];

        if (_appLaunchCounts.ContainsKey(app.Name)) _appLaunchCounts[app.Name]++;
        else _appLaunchCounts[app.Name] = 1;
        SaveStats();

        if (app.Hwnd != IntPtr.Zero)
        {
            ShowWindow(app.Hwnd, SW_RESTORE);
            SetForegroundWindow(app.Hwnd);
        }
        else if (!string.IsNullOrEmpty(app.Path))
        {
            try { Process.Start(new ProcessStartInfo(app.Path) { UseShellExecute = true }); } catch { }
        }
    }

    private void UpdateSystemStatus()
    {
        try
        {
            long bytesSent = 0, bytesReceived = 0;
            foreach (var ni in NetworkInterface.GetAllNetworkInterfaces())
            {
                if (ni.OperationalStatus == OperationalStatus.Up && ni.NetworkInterfaceType != NetworkInterfaceType.Loopback)
                {
                    var stats = ni.GetIPv4Statistics();
                    bytesSent += stats.BytesSent;
                    bytesReceived += stats.BytesReceived;
                }
            }
            if (_lastBytesSent > 0)
            {
                long diffRecv = bytesReceived - _lastBytesReceived;
                _netSpeedText.Text = $"{FormatSpeed(diffRecv)}↓";
            }
            _lastBytesSent = bytesSent;
            _lastBytesReceived = bytesReceived;
        }
        catch { }

        bool isFull = false;
        if (_isFullScreenHideEnabled)
        {
            try
            {
                SHQueryUserNotificationState(out var state);
                isFull = (state == QUERY_USER_NOTIFICATION_STATE.QUNS_BUSY ||
                          state == QUERY_USER_NOTIFICATION_STATE.QUNS_RUNNING_D3D_FULL_SCREEN ||
                          state == QUERY_USER_NOTIFICATION_STATE.QUNS_PRESENTATION_MODE);
            }
            catch { }

            if (!isFull)
            {
                IntPtr fg = GetForegroundWindow();
                if (fg != IntPtr.Zero && fg != _hwnd)
                {
                    try
                    {
                        uint pid;
                        GetWindowThreadProcessId(fg, out pid);
                        var proc = Process.GetProcessById((int)pid);
                        string pName = proc.ProcessName.ToLower();

                        if (!pName.Contains("explorer") && !pName.Contains("wallpaper") && !pName.Contains("desktop"))
                        {
                            if (GetWindowRect(fg, out RECT appRect))
                            {
                                IntPtr hMonitor = MonitorFromWindow(fg, 2);
                                MONITORINFO mi = new MONITORINFO { cbSize = Marshal.SizeOf(typeof(MONITORINFO)) };
                                if (GetMonitorInfo(hMonitor, ref mi))
                                {
                                    if (appRect.Left <= mi.rcMonitor.Left && appRect.Top <= mi.rcMonitor.Top &&
                                        appRect.Right >= mi.rcMonitor.Right && appRect.Bottom >= mi.rcMonitor.Bottom)
                                    {
                                        isFull = true;
                                    }
                                }
                            }
                        }
                    }
                    catch { }
                }
            }
        }

        if (isFull && !_isFullScreen) { _isFullScreen = true; this.Visibility = Visibility.Hidden; }
        else if (!isFull && _isFullScreen) { _isFullScreen = false; this.Visibility = Visibility.Visible; }

        UpdateNotificationBadge();
    }

    private async void UpdateNotificationBadge()
    {
        try
        {
            var listener = UserNotificationListener.Current;
            if (listener.GetAccessStatus() == UserNotificationListenerAccessStatus.Allowed)
            {
                var notifications = await listener.GetNotificationsAsync(NotificationKinds.Toast);
                int count = notifications.Count;
                Dispatcher.Invoke(() =>
                {
                    if (count > 0)
                    {
                        NotificationCountText.Text = count > 99 ? "99+" : count.ToString();
                        NotificationCountText.Visibility = Visibility.Visible;
                    }
                    else
                    {
                        NotificationCountText.Visibility = Visibility.Collapsed;
                    }
                });
            }
        }
        catch { }
    }

    private string FormatSpeed(long bytes)
    {
        if (bytes > 1024 * 1024) return $"{bytes / 1024.0 / 1024.0:F1}M";
        if (bytes > 1024) return $"{bytes / 1024.0:F0}K";
        return $"{bytes}B";
    }

    private void CheckVolumeChange()
    {
        try
        {
            var defAudio = AudioController.DefaultPlaybackDevice;
            double newVol = defAudio.Volume;
            if (Math.Abs(newVol - _currentVolume) > 1)
            {
                _currentVolume = newVol;
                ShowOsd($"🔊 音量: {newVol:F0}%");
            }
        }
        catch { }
    }

    private void ShowOsd(string text)
    {
        _isNotificationShowing = true;
        LyricBox.Text = text;
        LyricBox.Foreground = ColorAccent;
        LyricBox.Opacity = 1;
        _notificationTimer.Stop();
        _notificationTimer.Start();
    }

    private void InitTrayIcon()
    {
        var icon = Drawing.SystemIcons.Application;
        try
        {
            string exePath = Environment.ProcessPath ?? "";
            if (!string.IsNullOrEmpty(exePath) && File.Exists(exePath))
            {
                var extracted = Drawing.Icon.ExtractAssociatedIcon(exePath);
                if (extracted != null) icon = extracted;
            }
        }
        catch { }

        _notifyIcon = new WinForms.NotifyIcon
        {
            Icon = icon,
            Text = "Island 灵动岛",
            Visible = true
        };

        var contextMenu = new WinForms.ContextMenuStrip();
        var exitItem = new WinForms.ToolStripMenuItem("退出 Island", null, (_, _) =>
        {
            _notifyIcon.Visible = false;
            _notifyIcon.Dispose();
            Application.Current.Shutdown();
        });
        contextMenu.Items.Add(exitItem);
        _notifyIcon.ContextMenuStrip = contextMenu;
    }

    protected override void OnSourceInitialized(EventArgs e)
    {
        base.OnSourceInitialized(e);
        _hwnd = new WindowInteropHelper(this).Handle;
        SetWindowLong(_hwnd, GWL_EXSTYLE, GetWindowLong(_hwnd, GWL_EXSTYLE) | WS_EX_TOOLWINDOW);

        HwndSource source = HwndSource.FromHwnd(_hwnd);
        source.AddHook(WndProc);
        AddClipboardFormatListener(_hwnd);
    }

    protected override void OnClosed(EventArgs e)
    {
        RemoveClipboardFormatListener(_hwnd);
        _loopbackCapture?.StopRecording();
        _loopbackCapture?.Dispose();
        if (_notifyIcon != null)
        {
            _notifyIcon.Visible = false;
            _notifyIcon.Dispose();
        }
        base.OnClosed(e);
    }

    private IntPtr WndProc(IntPtr hwnd, int msg, IntPtr wParam, IntPtr lParam, ref bool handled)
    {
        if (msg == WM_CLIPBOARDUPDATE)
        {
            try
            {
                if (Clipboard.ContainsText())
                {
                    string text = Clipboard.GetText().Trim();
                    if (!string.IsNullOrEmpty(text) && (_clipboardHistory.Count == 0 || _clipboardHistory[0] != text))
                    {
                        _clipboardHistory.Insert(0, text);
                        if (_clipboardHistory.Count > 20) _clipboardHistory.RemoveAt(20);
                        if (_state == State.L3 && _currentPanelKey == "控制中心") OpenPanel("控制中心");
                    }
                }
            }
            catch { }
        }
        return IntPtr.Zero;
    }

    private void InitNotifications()
    {
        try
        {
            var listener = UserNotificationListener.Current;
            if (listener.GetAccessStatus() == UserNotificationListenerAccessStatus.Allowed)
                listener.NotificationChanged += OnNotificationChanged;
        }
        catch { }
    }

    private async void OnNotificationChanged(UserNotificationListener sender, UserNotificationChangedEventArgs args)
    {
        if (args.ChangeKind != UserNotificationChangedKind.Added) return;
        if (!_isNotificationInterruptEnabled) return;

        try
        {
            var notifications = await sender.GetNotificationsAsync(NotificationKinds.Toast);
            var latest = notifications.OrderByDescending(n => n.CreationTime).FirstOrDefault();
            if (latest != null && (DateTime.Now - latest.CreationTime).TotalSeconds < 5)
            {
                var textBinding = latest.Notification.Visual.GetBinding(KnownNotificationBindings.ToastGeneric);
                if (textBinding != null)
                {
                    var texts = textBinding.GetTextElements();
                    string title = texts.Count > 0 ? texts[0].Text : "";
                    string body = texts.Count > 1 ? texts[1].Text : "";
                    string appName = latest.AppInfo?.DisplayInfo?.DisplayName ?? "通知";
                    string msg = $"{title} {body}".Replace("\n", " ").Trim();
                    if (msg.Length > 20) msg = msg.Substring(0, 20) + "...";

                    Dispatcher.Invoke(() => {
                        _isNotificationShowing = true;
                        LyricBox.Text = $"📩 [{appName}] {msg}";
                        LyricBox.Foreground = ColorAccent;
                        LyricBox.Opacity = 1;
                        _notificationTimer.Stop();
                        _notificationTimer.Start();
                    });
                }
            }
        }
        catch { }
    }

    private void UpdateClock()
    {
        if (_isPomoRunning) return;
        TimeText.Text = DateTime.Now.ToString("HH:mm");
        if (Math.Abs(TimeText.ActualWidth - _mTime) > 1)
        {
            MeasureStaticElements();
            Relayout();
        }
    }

    private void StartPomodoro(int minutes)
    {
        _isPomoRunning = true;
        _pomoEndTime = DateTime.Now.AddMinutes(minutes);
        TimeText.Text = $"🍅 {minutes:00}:00";
        TimeText.FontSize = 13;
        _pomoTimer.Start();
    }

    private void UpdatePomodoro()
    {
        var remain = _pomoEndTime - DateTime.Now;
        if (remain.TotalSeconds <= 0)
        {
            _isPomoRunning = false;
            _pomoTimer.Stop();
            TimeText.FontSize = 15;
            UpdateClock();
            ShowOsd("🍅 专注时间结束！");
            Relayout();
        }
        else
        {
            TimeText.Text = $"🍅 {remain.Minutes:00}:{remain.Seconds:00}";
            Relayout();
        }
    }

    private void MeasureStaticElements()
    {
        TimeText.FontSize = 15; WeatherText.FontSize = 16;
        WifiIcon.FontSize = 18; SettingsIcon.FontSize = 18; BtIcon.FontSize = 18;
        NotificationIcon.FontSize = 18; MediaIcon.FontSize = 18; StartIcon.FontSize = 18;
        _netSpeedText.FontSize = 12;

        TimeText.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mTime = Math.Max(40, Math.Ceiling(TimeText.DesiredSize.Width) + 4);

        WeatherText.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mWeather = Math.Max(25, Math.Ceiling(WeatherText.DesiredSize.Width) + 4);

        WifiIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mWifi = Math.Ceiling(WifiIcon.DesiredSize.Width) + 4;

        SettingsIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mSettings = Math.Ceiling(SettingsIcon.DesiredSize.Width) + 4;

        BtIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mBt = Math.Ceiling(BtIcon.DesiredSize.Width) + 4;

        MediaIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mMedia = Math.Ceiling(MediaIcon.DesiredSize.Width) + 4;

        NotificationIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mNotif = Math.Ceiling(NotificationIcon.DesiredSize.Width) + 10;

        StartIcon.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
        _mStart = Math.Ceiling(StartIcon.DesiredSize.Width) + 4;
    }

    private async Task InitMediaManager()
    {
        try { _mediaManager = await GlobalSystemMediaTransportControlsSessionManager.RequestAsync(); }
        catch { }
    }

    private async Task CheckMediaStatus()
    {
        if (_mediaManager == null) return;
        try
        {
            _currentSession = _mediaManager.GetCurrentSession();
            if (_currentSession != null)
            {
                var playbackInfo = _currentSession.GetPlaybackInfo();
                _isSystemPlaying = playbackInfo.PlaybackStatus == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing;

                if (_isSystemPlaying)
                {
                    var mediaProps = await _currentSession.TryGetMediaPropertiesAsync();
                    if (mediaProps != null && !string.IsNullOrEmpty(mediaProps.Title))
                    {
                        bool wasPlaying = _isMediaPlaying;
                        _isMediaPlaying = true;

                        if (!wasPlaying)
                        {
                            if (_state == State.L1) AnimateTo(L1W, GetL1H(), 400, 400);
                            else if (_state == State.L2) AnimateTo(L2W, GetL2H(), 400, 400);
                        }

                        if (_currentSongName != mediaProps.Title + mediaProps.Artist)
                        {
                            _currentSongName = mediaProps.Title + mediaProps.Artist;
                            _currentTitle = mediaProps.Title;
                            _currentArtist = mediaProps.Artist;

                            if (mediaProps.Thumbnail != null)
                            {
                                try
                                {
                                    using var stream = await mediaProps.Thumbnail.OpenReadAsync();
                                    var bmp = new BitmapImage();
                                    bmp.BeginInit();
                                    bmp.StreamSource = stream.AsStreamForRead();
                                    bmp.CacheOption = BitmapCacheOption.OnLoad;
                                    bmp.EndInit();
                                    bmp.Freeze();
                                    _currentAlbumArt = bmp;
                                }
                                catch { _currentAlbumArt = null; }
                            }
                            else
                            {
                                _currentAlbumArt = null;
                            }

                            if (_state == State.L3 && _currentPanelKey == "音乐") LoadMusicPanel();
                            _ = FetchLyricsAsync(mediaProps.Title, mediaProps.Artist);
                        }

                        var timeline = _currentSession.GetTimelineProperties();
                        if (timeline != null)
                        {
                            _basePosition = timeline.Position;
                            _baseTime = DateTime.Now;
                        }
                        return;
                    }
                }
            }

            if (!_isSystemPlaying && _isMediaPlaying)
            {
                _isMediaPlaying = false;
                LyricBox.Opacity = 0;
                if (_state == State.L1) AnimateTo(L1W, GetL1H(), 400, 400);
                else if (_state == State.L2) AnimateTo(L2W, GetL2H(), 400, 400);
            }
        }
        catch { }
    }

    private async Task FetchLyricsAsync(string rawTitle, string rawArtist)
    {
        string requestSong = rawTitle + " - " + rawArtist;
        if (_currentRequestSong == requestSong) return;
        _currentRequestSong = requestSong;

        _lyrics.Clear();
        _currentLyricIndex = -1;
        LyricBox.Text = "正在加载歌词...";
        LyricBox.Foreground = ColorTextPrimary;

        try
        {
            using var client = new HttpClient();
            client.Timeout = TimeSpan.FromSeconds(4);
            client.DefaultRequestHeaders.Add("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
            client.DefaultRequestHeaders.Add("Referer", "http://music.163.com");

            string cleanTitle = Regex.Replace(rawTitle, @"[\(\[（【].*?[\)\]）】]", "").Trim();
            string cleanArtist = rawArtist.Split(new[] { ',', '/', '&', '、' })[0].Trim();

            long songId = await SearchSongId(client, $"{cleanTitle} {cleanArtist}");
            if (songId == -1) songId = await SearchSongId(client, cleanTitle);
            if (songId == -1) songId = await SearchSongId(client, $"{rawTitle} {rawArtist}");

            if (_currentRequestSong != requestSong) return;

            if (songId != -1)
            {
                var lyricUrl = $"http://music.163.com/api/song/lyric?id={songId}&lv=1&kv=1&tv=-1";
                var lyricJson = await client.GetStringAsync(lyricUrl);
                if (_currentRequestSong != requestSong) return;

                using var lyricDoc = JsonDocument.Parse(lyricJson);
                if (lyricDoc.RootElement.TryGetProperty("lrc", out var lrc) && lrc.TryGetProperty("lyric", out var lyricText))
                {
                    ParseLrc(lyricText.GetString());
                }
            }
            if (_lyrics.Count == 0 && _currentRequestSong == requestSong)
            {
                LyricBox.Text = "纯音乐，请欣赏";
                LyricBox.Foreground = ColorTextSecondary;
            }
        }
        catch
        {
            if (_currentRequestSong == requestSong && _lyrics.Count == 0)
            {
                LyricBox.Text = "暂无歌词";
                LyricBox.Foreground = ColorTextSecondary;
            }
        }
    }

    private async Task<long> SearchSongId(HttpClient client, string keyword)
    {
        try
        {
            var searchUrl = $"http://music.163.com/api/search/get/web?s={Uri.EscapeDataString(keyword)}&type=1&limit=1";
            var searchJson = await client.GetStringAsync(searchUrl);
            using var searchDoc = JsonDocument.Parse(searchJson);
            var result = searchDoc.RootElement.GetProperty("result");
            if (result.TryGetProperty("songs", out var songs) && songs.GetArrayLength() > 0)
                return songs[0].GetProperty("id").GetInt64();
        }
        catch { }
        return -1;
    }

    private void ParseLrc(string? lrcText)
    {
        if (string.IsNullOrEmpty(lrcText)) return;
        _lyrics.Clear();
        var lines = lrcText.Split('\n');
        var regex = new Regex(@"\[(\d{2}):(\d{2})\.(\d{2,3})\](.*)");
        foreach (var line in lines)
        {
            var match = regex.Match(line);
            if (match.Success)
            {
                int min = int.Parse(match.Groups[1].Value);
                int sec = int.Parse(match.Groups[2].Value);
                int ms = int.Parse(match.Groups[3].Value);
                if (match.Groups[3].Length == 2) ms *= 10;

                string text = match.Groups[4].Value.Trim();
                if (!string.IsNullOrEmpty(text)) _lyrics.Add((new TimeSpan(0, 0, min, sec, ms), text));
            }
        }
        _lyrics = _lyrics.OrderBy(l => l.Time).ToList();
    }

    private void UpdateLyricScroll()
    {
        if (_currentSession == null) return;
        try
        {
            if (_currentProgressBar != null)
            {
                var timeline = _currentSession.GetTimelineProperties();
                if (timeline != null && timeline.EndTime.TotalSeconds > 0) _currentProgressBar.Value = (timeline.Position.TotalSeconds / timeline.EndTime.TotalSeconds) * 100;
            }

            if (_lyrics.Count == 0) return;
            TimeSpan currentPos = _basePosition;
            if (_isSystemPlaying && _baseTime != DateTime.MinValue) currentPos += (DateTime.Now - _baseTime);

            int left = 0, right = _lyrics.Count - 1, index = -1;
            while (left <= right)
            {
                int mid = left + (right - left) / 2;
                if (_lyrics[mid].Time <= currentPos) { index = mid; left = mid + 1; }
                else right = mid - 1;
            }

            if (index != _currentLyricIndex && index >= 0)
            {
                _currentLyricIndex = index;
                if (!_isNotificationShowing)
                {
                    LyricBox.Text = _lyrics[index].Text;
                    LyricBox.Foreground = ColorTextPrimary;
                    LyricBox.Opacity = 1;
                }

                if (_lyricStack.Children.Count > 0 && _state == State.L3)
                {
                    for (int i = 0; i < _lyricStack.Children.Count; i++)
                    {
                        if (_lyricStack.Children[i] is TextBlock tb)
                        {
                            if (i == _currentLyricIndex) { tb.Foreground = ColorTextPrimary; tb.FontWeight = FontWeights.Bold; tb.FontSize = 18; }
                            else { tb.Foreground = ColorTextSecondary; tb.FontWeight = FontWeights.Normal; tb.FontSize = 14; }
                        }
                    }
                }
            }
        }
        catch { }
    }

    private void LoadConfig()
    {
        try
        {
            using var key = Registry.CurrentUser.OpenSubKey(@"Software\IslandWidget", false);
            if (key?.GetValue("CustomLocation") is string loc && !string.IsNullOrWhiteSpace(loc)) _customLocation = loc;
        }
        catch { }
    }

    private void SaveConfig()
    {
        try
        {
            using var key = Registry.CurrentUser.CreateSubKey(@"Software\IslandWidget");
            key?.SetValue("CustomLocation", _customLocation);
        }
        catch { }
    }

    private async Task RequestWinRTPermissions()
    {
        try
        {
            await Radio.RequestAccessAsync();
            await UserNotificationListener.Current.RequestAccessAsync();
            await Windows.Devices.Geolocation.Geolocator.RequestAccessAsync();
        }
        catch { }
    }

    private void BuildWindowIcons()
    {
        for (int i = 0; i < 5; i++)
        {
            var img = new Image { Stretch = Stretch.Uniform, Margin = new Thickness(2) };
            _windowImages[i] = img;
            var b = new Border { Child = img, Opacity = i < 3 ? 1 : 0, Cursor = Cursors.Hand, Background = Brushes.Transparent, CornerRadius = new CornerRadius(4) };
            int index = i;
            b.MouseLeftButtonDown += (_, _) => FocusWindow(index);
            _windowIcons[i] = b;
        }
    }

    private ImageSource? GetWindowIcon(IntPtr hwnd)
    {
        IntPtr hIcon = SendMessage(hwnd, WM_GETICON, (IntPtr)ICON_SMALL2, IntPtr.Zero);
        if (hIcon == IntPtr.Zero) hIcon = GetClassLongPtr(hwnd, GCLP_HICONSM);
        if (hIcon != IntPtr.Zero)
        {
            var img = Imaging.CreateBitmapSourceFromHIcon(hIcon, Int32Rect.Empty, BitmapSizeOptions.FromEmptyOptions());
            img.Freeze();
            return img;
        }
        return null;
    }

    private IntPtr GetClassLongPtr(IntPtr hWnd, int nIndex)
    {
        return IntPtr.Size == 8 ? GetClassLongPtr64(hWnd, nIndex) : GetClassLongPtr32(hWnd, nIndex);
    }

    private void Relayout()
    {
        double w = Width, h = Height;
        if (w <= 0 || h <= 0) return;

        double p = Math.Clamp((w - L1W) / (L2W - L1W), 0, 1);

        double pad = 16;
        double topY = 4 + (4 * p);

        Canvas.SetTop(TimeBox, topY); Canvas.SetTop(WeatherBox, topY); Canvas.SetTop(WifiBox, topY);
        Canvas.SetTop(SettingsBox, topY); Canvas.SetTop(BtBox, topY); Canvas.SetTop(MediaBox, topY);
        Canvas.SetTop(NotificationBox, topY); Canvas.SetTop(StartBox, topY);
        Canvas.SetTop(_netSpeedBox, topY);

        double currentX = pad;
        Canvas.SetLeft(TimeBox, currentX); currentX += _mTime + 6;
        Canvas.SetLeft(_netSpeedBox, currentX); currentX += _mNetSpeed + 6;
        Canvas.SetLeft(WeatherBox, currentX); currentX += _mWeather + 6;

        SettingsBox.Width = _mSettings * p; SettingsBox.Opacity = p;
        Canvas.SetLeft(SettingsBox, currentX); currentX += SettingsBox.Width + (6 * p);

        BtBox.Width = _mBt * p; BtBox.Opacity = p;
        Canvas.SetLeft(BtBox, currentX); currentX += BtBox.Width + (6 * p);

        Canvas.SetLeft(WifiBox, currentX); currentX += _mWifi + (6 * p);

        Canvas.SetLeft(NotificationBox, currentX); currentX += _mNotif + (6 * p);

        MediaBox.Width = _mMedia * p; MediaBox.Opacity = p;
        Canvas.SetLeft(MediaBox, currentX); currentX += MediaBox.Width + (6 * p);

        StartBox.Width = _mStart * p; StartBox.Opacity = p;
        Canvas.SetLeft(StartBox, currentX); currentX += StartBox.Width + (6 * p);

        double rightStartX = currentX;
        double iconSize = 18 + (4 * p);
        double iconGap = 6 + (4 * p);
        double currentRight = rightStartX;

        for (int i = 0; i < 5; i++)
        {
            var b = _windowIcons[i];
            b.Width = iconSize; b.Height = iconSize;

            if (i < 3)
            {
                Canvas.SetLeft(b, currentRight);
                Canvas.SetTop(b, (24 - iconSize) / 2 + topY);
                b.Opacity = 1;
                currentRight += iconSize + iconGap;
            }
            else
            {
                if (p > 0.1)
                {
                    Canvas.SetLeft(b, currentRight);
                    Canvas.SetTop(b, (24 - iconSize) / 2 + topY);
                    b.Opacity = p;
                    currentRight += iconSize + iconGap;
                }
                else
                {
                    b.Opacity = 0;
                }
            }
            if (b.Parent == null) Stage.Children.Add(b);
        }

        if (_isMediaPlaying && h < L3H)
        {
            LyricBox.FontSize = 14; LyricBox.Width = w - 2 * pad;
            Canvas.SetLeft(LyricBox, pad);
            Canvas.SetTop(LyricBox, 30);
            if (!_isNotificationShowing) LyricBox.Opacity = 1;
        }
        else if (!_isPomoRunning) LyricBox.Opacity = 0;

        double panelTop = GetL2H();
        double panelH = Math.Max(0, h - panelTop);
        Panel.Width = w - 2; Panel.Height = panelH;
        Canvas.SetLeft(Panel, 1); Canvas.SetTop(Panel, panelTop);
        Panel.Opacity = Math.Clamp((h - panelTop) / (L3H - panelTop), 0, 1);

        var wa = SystemParameters.WorkArea;
        Left = wa.Left + (wa.Width - w) / 2;
        Top = wa.Top + TopMargin;
    }

    private void OnMouseEnter()
    {
        if (_state == State.L1)
        {
            _state = State.L2;
            AnimateTo(L2W, GetL2H(), 400, 400);
        }
        else if (_state == State.L2)
        {
            _leaveL2Timer.Stop();
        }
        else if (_state == State.L3) { _closeTimer.Stop(); }
    }

    private void OnMouseLeave()
    {
        if (_state == State.L2)
        {
            _leaveL2Timer.Stop();
            _leaveL2Timer.Start();
        }
        else if (_state == State.L3) { _closeTimer.Stop(); _closeTimer.Start(); }
    }

    private async void OpenPanel(string key)
    {
        _state = State.L3; _closeTimer.Stop();
        _currentPanelKey = key;
        _panelGeneration++;

        PanelContent.Children.Clear();

        var title = new TextBlock { Text = key, Foreground = ColorTextPrimary, FontSize = 20, FontWeight = FontWeights.Bold, Margin = new Thickness(0, 0, 0, 15) };
        PanelContent.Children.Add(title);

        if (key == "WiFi") await LoadRadioPanel(RadioKind.WiFi);
        else if (key == "蓝牙") await LoadRadioPanel(RadioKind.Bluetooth);
        else if (key == "通知") await LoadNotificationPanel();
        else if (key == "设置") LoadSettingsPanel();
        else if (key == "天气") LoadWeatherPanel();
        else if (key == "音乐") LoadMusicPanel();
        else if (key == "控制中心") LoadControlCenter();
        else if (key == "应用") LoadAppsPanel();

        AnimateTo(L2W, L3H, 400, 800);
    }

    private Border CreateCard(UIElement content)
    {
        return new Border { Background = ColorCardBg, CornerRadius = new CornerRadius(12), Padding = new Thickness(15), Margin = new Thickness(0, 0, 0, 10), Child = content };
    }

    private Button CreateListItemButton(string text, string tag)
    {
        var btn = new Button
        {
            Content = new TextBlock { Text = text, Foreground = ColorTextPrimary, FontSize = 14, TextTrimming = TextTrimming.CharacterEllipsis },
            Background = Brushes.Transparent,
            HorizontalContentAlignment = HorizontalAlignment.Left,
            Padding = new Thickness(10, 8, 10, 8),
            Margin = new Thickness(0, 0, 0, 2),
            BorderThickness = new Thickness(0),
            Cursor = Cursors.Hand,
        };
        btn.MouseEnter += (_, _) => btn.Background = ColorHoverBg;
        btn.MouseLeave += (_, _) => btn.Background = Brushes.Transparent;
        return btn;
    }

    private void LoadControlCenter()
    {
        var searchPanel = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 10) };
        var searchBox = new TextBox { Width = 200, Padding = new Thickness(5), Background = ColorCardBg, Foreground = ColorTextPrimary, BorderThickness = new Thickness(0), CaretBrush = ColorTextPrimary };
        var searchBtn = new Button { Content = "极速搜索", Background = ColorAccent, Foreground = Brushes.White, Padding = new Thickness(10, 5, 10, 5), BorderThickness = new Thickness(0), Margin = new Thickness(5, 0, 0, 0) };
        searchBtn.Click += (_, _) => Process.Start(new ProcessStartInfo($"https://www.bing.com/search?q={Uri.EscapeDataString(searchBox.Text)}") { UseShellExecute = true });
        SetupTextBox(searchBox, (val) => { });
        searchPanel.Children.Add(searchBox); searchPanel.Children.Add(searchBtn);
        PanelContent.Children.Add(CreateCard(searchPanel));

        var aiPanel = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 10) };
        var transBtn = new Button { Content = "🌐 AI 翻译剪贴板", Background = ColorCardBg, Foreground = ColorTextPrimary, Padding = new Thickness(10, 5, 10, 5), BorderThickness = new Thickness(0) };
        transBtn.Click += async (_, _) => {
            string text = Clipboard.GetText();
            if (string.IsNullOrWhiteSpace(text)) return;
            ShowOsd("正在翻译...");
            var result = await TranslateText(text);
            ShowOsd($"翻译: {result}");
        };
        aiPanel.Children.Add(transBtn);
        PanelContent.Children.Add(CreateCard(aiPanel));

        var pomoPanel = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 15) };
        pomoPanel.Children.Add(new TextBlock { Text = "🍅 番茄钟: ", Foreground = ColorTextPrimary, VerticalAlignment = VerticalAlignment.Center });
        if (_isPomoRunning)
        {
            var stopBtn = new Button { Content = "停止专注", Background = ColorRed, Foreground = Brushes.White, Padding = new Thickness(10, 5, 10, 5), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
            stopBtn.Click += (_, _) => { _isPomoRunning = false; _pomoTimer.Stop(); TimeText.FontSize = 15; UpdateClock(); OpenPanel("控制中心"); };
            pomoPanel.Children.Add(stopBtn);
        }
        else
        {
            var pomoTb = new TextBox { Text = "25", Width = 40, Background = ColorCardBg, Foreground = ColorTextPrimary, BorderThickness = new Thickness(0), VerticalContentAlignment = VerticalAlignment.Center, TextAlignment = TextAlignment.Center, Margin = new Thickness(0, 0, 5, 0) };
            SetupTextBox(pomoTb, (val) => { });
            pomoPanel.Children.Add(pomoTb);
            pomoPanel.Children.Add(new TextBlock { Text = " 分钟", Foreground = ColorTextPrimary, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(0, 0, 10, 0) });
            var startBtn = new Button { Content = "启动", Background = ColorAccent, Foreground = Brushes.White, Padding = new Thickness(10, 5, 10, 5), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
            startBtn.Click += (_, _) => { if (int.TryParse(pomoTb.Text, out int mins) && mins > 0) { StartPomodoro(mins); OpenPanel("控制中心"); } };
            pomoPanel.Children.Add(startBtn);
        }
        PanelContent.Children.Add(pomoPanel);

        var toolsWrap = new WrapPanel();
        var snapBtn = new Button { Content = "截图", Background = ColorCardBg, Foreground = ColorTextPrimary, Padding = new Thickness(10), Margin = new Thickness(0, 0, 5, 5), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
        snapBtn.Click += (_, _) => Process.Start(new ProcessStartInfo("ms-screenclip:") { UseShellExecute = true });
        var recycleBtn = new Button { Content = "清空回收站", Background = ColorCardBg, Foreground = ColorTextPrimary, Padding = new Thickness(10), Margin = new Thickness(0, 0, 5, 5), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
        recycleBtn.Click += (_, _) => SHEmptyRecycleBin(IntPtr.Zero, null!, 0);
        toolsWrap.Children.Add(snapBtn); toolsWrap.Children.Add(recycleBtn);
        PanelContent.Children.Add(toolsWrap);

        PanelContent.Children.Add(new TextBlock { Text = "剪贴板历史", Foreground = ColorTextSecondary, FontSize = 12, Margin = new Thickness(0, 10, 0, 5) });
        if (_clipboardHistory.Count == 0) PanelContent.Children.Add(new TextBlock { Text = "暂无历史", Foreground = ColorTextSecondary, FontSize = 12 });
        else
        {
            foreach (var item in _clipboardHistory.Take(3))
            {
                string display = item.Replace("\n", " ");
                if (display.Length > 30) display = display.Substring(0, 30) + "...";
                var btn = CreateListItemButton(display, item);
                btn.Click += (_, _) => { Clipboard.SetText(item); ShowOsd("已复制到剪贴板"); };
                PanelContent.Children.Add(btn);
            }
        }

        var appBtn = CreateListItemButton("查看所有程序", "");
        appBtn.Click += (_, _) => OpenPanel("应用");
        PanelContent.Children.Add(appBtn);
    }

    private async Task<string> TranslateText(string text)
    {
        try
        {
            using var client = new HttpClient();
            var res = await client.GetStringAsync($"https://v.api.aa1.cn/api/api-fanyi-rm-ms/index.php?msg={Uri.EscapeDataString(text)}");
            if (!string.IsNullOrEmpty(res)) return res.Trim();
        }
        catch { }
        return "网络异常，翻译失败";
    }

    private async void LoadAppsPanel()
    {
        int currentGen = ++_panelGeneration;
        var loadingText = new TextBlock { Text = "正在扫描应用程序...", Foreground = ColorTextSecondary };
        PanelContent.Children.Add(loadingText);

        List<(string Name, string Path)> apps;
        try
        {
            apps = await Task.Run(() =>
            {
                var list = new List<(string Name, string Path)>();
                var seenNames = new HashSet<string>();
                string[] dirs = {
                    Environment.GetFolderPath(Environment.SpecialFolder.CommonStartMenu) + "\\Programs",
                    Environment.GetFolderPath(Environment.SpecialFolder.StartMenu) + "\\Programs",
                    Environment.GetFolderPath(Environment.SpecialFolder.Desktop),
                    Environment.GetFolderPath(Environment.SpecialFolder.CommonDesktopDirectory)
                };

                foreach (var dir in dirs)
                {
                    if (!Directory.Exists(dir)) continue;
                    try
                    {
                        var files = Directory.EnumerateFiles(dir, "*.*", SearchOption.AllDirectories);
                        foreach (var f in files)
                        {
                            try
                            {
                                if (f.EndsWith(".lnk", StringComparison.OrdinalIgnoreCase) || f.EndsWith(".url", StringComparison.OrdinalIgnoreCase) || f.EndsWith(".exe", StringComparison.OrdinalIgnoreCase))
                                {
                                    var name = System.IO.Path.GetFileNameWithoutExtension(f);
                                    if (string.IsNullOrWhiteSpace(name) || name.StartsWith(".")) continue;
                                    if (seenNames.Add(name)) list.Add((name, f));
                                }
                            }
                            catch { }
                        }
                    }
                    catch { }
                }
                return list.OrderBy(x => x.Name).Take(100).ToList();
            });
        }
        catch (Exception ex)
        {
            PanelContent.Children.Clear();
            PanelContent.Children.Add(new TextBlock { Text = "扫描出错: " + ex.Message, Foreground = ColorRed });
            return;
        }

        if (currentGen != _panelGeneration) return;
        PanelContent.Children.Remove(loadingText);

        if (apps.Count == 0)
        {
            PanelContent.Children.Add(new TextBlock { Text = "未扫描到应用", Foreground = ColorTextSecondary, Margin = new Thickness(10) });
            return;
        }

        var wrap = new WrapPanel { HorizontalAlignment = HorizontalAlignment.Center };
        foreach (var app in apps)
        {
            var item = new Button { Width = 76, Height = 85, Background = Brushes.Transparent, BorderThickness = new Thickness(0), Cursor = Cursors.Hand, Margin = new Thickness(2) };
            var stack = new StackPanel { HorizontalAlignment = HorizontalAlignment.Center };
            var img = new Image { Width = 36, Height = 36, Source = GetFileIcon(app.Path), Margin = new Thickness(0, 0, 0, 6) };
            var txt = new TextBlock { Text = app.Name, Foreground = ColorTextPrimary, FontSize = 11, TextAlignment = TextAlignment.Center, TextTrimming = TextTrimming.CharacterEllipsis, MaxWidth = 72 };
            stack.Children.Add(img); stack.Children.Add(txt); item.Content = stack;

            item.MouseEnter += (_, _) => item.Background = ColorHoverBg;
            item.MouseLeave += (_, _) => item.Background = Brushes.Transparent;
            item.Click += (_, _) => { try { Process.Start(new ProcessStartInfo(app.Path) { UseShellExecute = true }); } catch { } };
            wrap.Children.Add(item);
        }
        PanelContent.Children.Add(wrap);
    }

    private ImageSource? GetFileIcon(string path)
    {
        try
        {
            SHFILEINFO shinfo = new SHFILEINFO();
            IntPtr hImg = SHGetFileInfo(path, 0, out shinfo, (uint)Marshal.SizeOf(shinfo), SHGFI_ICON | SHGFI_LARGEICON);
            if (shinfo.hIcon != IntPtr.Zero)
            {
                var img = Imaging.CreateBitmapSourceFromHIcon(shinfo.hIcon, Int32Rect.Empty, BitmapSizeOptions.FromEmptyOptions());
                img.Freeze(); DestroyIcon(shinfo.hIcon);
                return img;
            }
        }
        catch { }
        return null;
    }

    private void LoadMusicPanel()
    {
        if (!_isMediaPlaying || _currentSession == null) { PanelContent.Children.Add(new TextBlock { Text = "当前没有播放音乐", Foreground = ColorTextSecondary }); return; }

        var headerGrid = new Grid { Margin = new Thickness(0, 0, 0, 15) };
        headerGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
        headerGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });

        if (_currentAlbumArt != null)
        {
            var img = new Image { Source = _currentAlbumArt, Width = 64, Height = 64, Stretch = Stretch.UniformToFill };
            img.Clip = new RectangleGeometry(new Rect(0, 0, 64, 64), 12, 12);
            headerGrid.Children.Add(img);
        }
        else
        {
            var fallback = new Border { Width = 64, Height = 64, Background = ColorHoverBg, CornerRadius = new CornerRadius(12), Child = new TextBlock { Text = "🎵", FontSize = 28, HorizontalAlignment = HorizontalAlignment.Center, VerticalAlignment = VerticalAlignment.Center } };
            headerGrid.Children.Add(fallback);
        }

        var infoStack = new StackPanel { Margin = new Thickness(15, 0, 0, 0), VerticalAlignment = VerticalAlignment.Center };
        _titleTextBlock = new TextBlock { Text = _currentTitle, Foreground = ColorTextPrimary, FontSize = 18, FontWeight = FontWeights.Bold, TextTrimming = TextTrimming.CharacterEllipsis };
        _artistTextBlock = new TextBlock { Text = _currentArtist, Foreground = ColorTextSecondary, FontSize = 13, Margin = new Thickness(0, 4, 0, 0) };
        _currentProgressBar = new ProgressBar { Height = 4, Margin = new Thickness(0, 10, 0, 0), Background = ColorCardBg, Foreground = ColorAccent, BorderThickness = new Thickness(0), MinHeight = 4 };

        infoStack.Children.Add(_titleTextBlock); infoStack.Children.Add(_artistTextBlock); infoStack.Children.Add(_currentProgressBar);
        Grid.SetColumn(infoStack, 1); headerGrid.Children.Add(infoStack);
        PanelContent.Children.Add(headerGrid);

        _visualizerCanvas = new Canvas { Height = 40, Margin = new Thickness(0, 0, 0, 10), HorizontalAlignment = HorizontalAlignment.Center };
        double barWidth = 10;
        double spacing = 15;
        double startX = (L2W - 40 - (16 * spacing)) / 2;

        for (int i = 0; i < 16; i++)
        {
            var rect = new Rectangle { Width = barWidth, Height = 2, Fill = ColorAccent, RadiusX = 2, RadiusY = 2 };
            Canvas.SetLeft(rect, startX + i * spacing);
            Canvas.SetTop(rect, 38);
            _visualizerCanvas.Children.Add(rect);
        }
        PanelContent.Children.Add(_visualizerCanvas);

        var scroll = new ScrollViewer { Height = 130, VerticalScrollBarVisibility = ScrollBarVisibility.Hidden };
        _lyricStack = new StackPanel { Margin = new Thickness(0, 20, 0, 20) };
        foreach (var ly in _lyrics) _lyricStack.Children.Add(new TextBlock { Text = ly.Text, Foreground = ColorTextSecondary, FontSize = 14, Margin = new Thickness(0, 6, 0, 6), TextWrapping = TextWrapping.Wrap, TextAlignment = TextAlignment.Center });
        if (_lyrics.Count == 0) _lyricStack.Children.Add(new TextBlock { Text = "暂无歌词", Foreground = ColorTextSecondary, TextAlignment = TextAlignment.Center });
        scroll.Content = _lyricStack;

        var lyricGrid = new Grid();
        lyricGrid.Children.Add(scroll);
        var topMask = new Border { Height = 30, VerticalAlignment = VerticalAlignment.Top, IsHitTestVisible = false, Background = new LinearGradientBrush(Color.FromArgb(230, 0, 0, 0), Color.FromArgb(0, 0, 0, 0), 90) };
        var bottomMask = new Border { Height = 30, VerticalAlignment = VerticalAlignment.Bottom, IsHitTestVisible = false, Background = new LinearGradientBrush(Color.FromArgb(0, 0, 0, 0), Color.FromArgb(230, 0, 0, 0), 90) };
        lyricGrid.Children.Add(topMask); lyricGrid.Children.Add(bottomMask);
        PanelContent.Children.Add(lyricGrid);

        var ctrlStack = new StackPanel { Orientation = Orientation.Horizontal, HorizontalAlignment = HorizontalAlignment.Center, Margin = new Thickness(0, 10, 0, 0) };
        var btnPrev = CreateRoundMediaBtn("\uE892", 44);
        var btnPlay = CreateRoundMediaBtn("\uE769", 56);
        var btnNext = CreateRoundMediaBtn("\uE893", 44);

        btnPrev.Click += async (_, _) => await _currentSession.TrySkipPreviousAsync();
        btnPlay.Click += async (_, _) => {
            var info = _currentSession.GetPlaybackInfo();
            if (info.PlaybackStatus == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing) await _currentSession.TryPauseAsync();
            else await _currentSession.TryPlayAsync();
        };
        btnNext.Click += async (_, _) => await _currentSession.TrySkipNextAsync();

        ctrlStack.Children.Add(btnPrev); ctrlStack.Children.Add(btnPlay); ctrlStack.Children.Add(btnNext);
        PanelContent.Children.Add(ctrlStack);

        _currentLyricIndex = -1;
    }

    private Button CreateRoundMediaBtn(string glyph, int size)
    {
        var border = new Border { Background = ColorCardBg, CornerRadius = new CornerRadius(size / 2.0) };
        border.Child = new TextBlock { Text = glyph, FontFamily = new FontFamily("Segoe MDL2 Assets"), Foreground = ColorTextPrimary, FontSize = size * 0.35, HorizontalAlignment = HorizontalAlignment.Center, VerticalAlignment = VerticalAlignment.Center };
        var btn = new Button { Content = border, Width = size, Height = size, Background = Brushes.Transparent, BorderThickness = new Thickness(0), Cursor = Cursors.Hand, Margin = new Thickness(10, 0, 10, 0) };
        btn.MouseEnter += (_, _) => border.Background = ColorHoverBg;
        btn.MouseLeave += (_, _) => border.Background = ColorCardBg;
        return btn;
    }

    // ==== 补全 LoadWeatherPanel 方法 ====
    private void LoadWeatherPanel()
    {
        var locStack = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 10) };
        locStack.Children.Add(new TextBlock { Text = "📍 ", Foreground = ColorTextSecondary, FontSize = 12, VerticalAlignment = VerticalAlignment.Center });
        var locInput = new TextBox { Text = _customLocation, Foreground = ColorTextSecondary, Background = Brushes.Transparent, BorderThickness = new Thickness(0), FontSize = 12, VerticalContentAlignment = VerticalAlignment.Center, Cursor = Cursors.IBeam, Width = 120 };
        SetupTextBox(locInput, (val) => {
            if (!string.IsNullOrWhiteSpace(val) && _customLocation != val)
            {
                _customLocation = val;
                SaveConfig();
                FetchWeatherDataAsync();
            }
        });
        locStack.Children.Add(locInput); PanelContent.Children.Add(locStack);

        var mainGrid = new Grid();
        mainGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
        mainGrid.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1.3, GridUnitType.Star) });

        var leftStack = new StackPanel { VerticalAlignment = VerticalAlignment.Center };
        leftStack.Children.Add(new TextBlock { Text = $"{_currentWeather.CurrentTemp}°", Foreground = ColorTextPrimary, FontSize = 52, FontWeight = FontWeights.Light, FontFamily = new FontFamily("Bahnschrift") });
        leftStack.Children.Add(new TextBlock { Text = GetWeatherDesc(_currentWeather.CurrentCode), Foreground = ColorTextPrimary, FontSize = 16, Margin = new Thickness(0, 0, 0, 5) });
        leftStack.Children.Add(new TextBlock { Text = $"💧 湿度 {_currentWeather.Humidity}%   🌬️ 风速 {_currentWeather.WindSpeed}km/h", Foreground = ColorTextSecondary, FontSize = 12 });
        Grid.SetColumn(leftStack, 0); mainGrid.Children.Add(leftStack);

        var rightStack = new StackPanel { Margin = new Thickness(10, 0, 0, 0) };
        if (_currentWeather.Daily.Count > 0)
        {
            for (int i = 0; i < Math.Min(7, _currentWeather.Daily.Count); i++)
            {
                var day = _currentWeather.Daily[i];
                var row = new Grid { Margin = new Thickness(0, 4, 0, 4) };
                row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(40) });
                row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
                row.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(70) });

                row.Children.Add(new TextBlock { Text = FormatDate(day.Date, i), Foreground = ColorTextPrimary, VerticalAlignment = VerticalAlignment.Center, FontSize = 12 });

                var bar = new Border { Height = 4, Background = ColorCardBg, CornerRadius = new CornerRadius(2), Margin = new Thickness(5, 0, 5, 0), VerticalAlignment = VerticalAlignment.Center };
                Grid.SetColumn(bar, 1); row.Children.Add(bar);

                var temps = new TextBlock { Text = $"{day.MaxTemp}° / {day.MinTemp}°", Foreground = ColorTextPrimary, VerticalAlignment = VerticalAlignment.Center, HorizontalAlignment = HorizontalAlignment.Right, FontSize = 12 };
                Grid.SetColumn(temps, 2); row.Children.Add(temps);

                rightStack.Children.Add(row);
            }
        }
        else
        {
            rightStack.Children.Add(new TextBlock { Text = "正在获取天气预报...", Foreground = ColorTextSecondary, FontSize = 12 });
        }

        Grid.SetColumn(rightStack, 1); mainGrid.Children.Add(rightStack);
        PanelContent.Children.Add(CreateCard(mainGrid));
    }

    private void LoadSettingsPanel()
    {
        var islandSettings = new StackPanel();

        // 1. 开机自启
        var startupRow = new Grid { Margin = new Thickness(0, 5, 0, 5) };
        startupRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
        startupRow.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
        startupRow.Children.Add(new TextBlock { Text = "开机自动启动", Foreground = ColorTextPrimary, FontSize = 14, VerticalAlignment = VerticalAlignment.Center });

        var startupBtn = new Button
        {
            Content = _isStartupEnabled ? "已开启" : "已关闭",
            Background = _isStartupEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60)),
            Foreground = Brushes.White,
            Padding = new Thickness(15, 5, 15, 5),
            BorderThickness = new Thickness(0),
            Cursor = Cursors.Hand
        };
        startupBtn.Click += (_, _) => {
            _isStartupEnabled = !_isStartupEnabled;
            SetStartup(_isStartupEnabled);
            // 直接更新当前按钮的样式，绝不刷新整个面板
            startupBtn.Content = _isStartupEnabled ? "已开启" : "已关闭";
            startupBtn.Background = _isStartupEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60));
        };
        Grid.SetColumn(startupBtn, 1); startupRow.Children.Add(startupBtn);
        islandSettings.Children.Add(startupRow);

        // 2. 全屏隐藏
        var fullRow = new Grid { Margin = new Thickness(0, 5, 0, 5) };
        fullRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
        fullRow.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
        fullRow.Children.Add(new TextBlock { Text = "全屏时自动隐藏", Foreground = ColorTextPrimary, FontSize = 14, VerticalAlignment = VerticalAlignment.Center });

        var fullBtn = new Button
        {
            Content = _isFullScreenHideEnabled ? "已开启" : "已关闭",
            Background = _isFullScreenHideEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60)),
            Foreground = Brushes.White,
            Padding = new Thickness(15, 5, 15, 5),
            BorderThickness = new Thickness(0),
            Cursor = Cursors.Hand
        };
        fullBtn.Click += (_, _) => {
            _isFullScreenHideEnabled = !_isFullScreenHideEnabled;
            fullBtn.Content = _isFullScreenHideEnabled ? "已开启" : "已关闭";
            fullBtn.Background = _isFullScreenHideEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60));
        };
        Grid.SetColumn(fullBtn, 1); fullRow.Children.Add(fullBtn);
        islandSettings.Children.Add(fullRow);

        // 3. 消息打断
        var notifRow = new Grid { Margin = new Thickness(0, 5, 0, 5) };
        notifRow.ColumnDefinitions.Add(new ColumnDefinition { Width = new GridLength(1, GridUnitType.Star) });
        notifRow.ColumnDefinitions.Add(new ColumnDefinition { Width = GridLength.Auto });
        notifRow.Children.Add(new TextBlock { Text = "消息通知打断", Foreground = ColorTextPrimary, FontSize = 14, VerticalAlignment = VerticalAlignment.Center });

        var notifBtn = new Button
        {
            Content = _isNotificationInterruptEnabled ? "已开启" : "已关闭",
            Background = _isNotificationInterruptEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60)),
            Foreground = Brushes.White,
            Padding = new Thickness(15, 5, 15, 5),
            BorderThickness = new Thickness(0),
            Cursor = Cursors.Hand
        };
        notifBtn.Click += (_, _) => {
            _isNotificationInterruptEnabled = !_isNotificationInterruptEnabled;
            notifBtn.Content = _isNotificationInterruptEnabled ? "已开启" : "已关闭";
            notifBtn.Background = _isNotificationInterruptEnabled ? ColorAccent : new SolidColorBrush(Color.FromRgb(60, 60, 60));
        };
        Grid.SetColumn(notifBtn, 1); notifRow.Children.Add(notifBtn);
        islandSettings.Children.Add(notifRow);

        PanelContent.Children.Add(new TextBlock { Text = "灵动岛设置", Foreground = ColorTextSecondary, FontSize = 12, Margin = new Thickness(0, 0, 0, 5) });
        PanelContent.Children.Add(CreateCard(islandSettings));

        // 硬件与系统控制 (保持不变)
        var battery = Battery.AggregateBattery.GetReport();
        string batteryText = "未知";
        if (battery.FullChargeCapacityInMilliwattHours.HasValue && battery.RemainingCapacityInMilliwattHours.HasValue)
        {
            double full = battery.FullChargeCapacityInMilliwattHours.Value;
            double remaining = battery.RemainingCapacityInMilliwattHours.Value;
            double percent = remaining / full * 100;
            batteryText = $"电池电量: {percent:F0}% ({(battery.Status == Windows.System.Power.BatteryStatus.Charging ? "充电中" : "使用中")})";
        }
        var sysStack = new StackPanel();
        sysStack.Children.Add(new TextBlock { Text = batteryText, Foreground = ColorTextPrimary, FontSize = 14 });
        PanelContent.Children.Add(CreateCard(sysStack));

        var controlStack = new StackPanel();
        var defAudio = AudioController.DefaultPlaybackDevice;
        controlStack.Children.Add(new TextBlock { Text = $"🔊 音量 ({defAudio.Volume:F0}%)", Foreground = ColorTextPrimary, Margin = new Thickness(0, 0, 0, 5) });
        var volSlider = new Slider { Minimum = 0, Maximum = 100, Value = defAudio.Volume, Margin = new Thickness(0, 0, 0, 15) };
        volSlider.ValueChanged += (_, e) => { defAudio.Volume = e.NewValue; ((TextBlock)controlStack.Children[0]).Text = $"🔊 音量 ({e.NewValue:F0}%)"; };
        controlStack.Children.Add(volSlider);

        var brightLabel = new TextBlock { Text = "☀️ 亮度 (读取中...)", Foreground = ColorTextPrimary, Margin = new Thickness(0, 0, 0, 5) };
        var brightSlider = new Slider { Minimum = 0, Maximum = 100, Value = 50, IsEnabled = false, Margin = new Thickness(0, 0, 0, 5) };
        brightSlider.ValueChanged += (_, e) => { if (brightSlider.IsEnabled) SetBrightness((int)e.NewValue); };
        brightSlider.AddHandler(Slider.PreviewMouseLeftButtonUpEvent, new MouseButtonEventHandler((_, _) => { brightLabel.Text = $"☀️ 亮度 ({brightSlider.Value:F0}%)"; }));
        controlStack.Children.Add(brightLabel); controlStack.Children.Add(brightSlider);

        _ = Task.Run(() => {
            int b = GetBrightness();
            Dispatcher.Invoke(() => {
                if (b >= 0) { brightLabel.Text = $"☀️ 亮度 ({b}%)"; brightSlider.Value = b; brightSlider.IsEnabled = true; }
                else { brightLabel.Text = "☀️ 亮度 (该屏幕不支持)"; brightLabel.Foreground = ColorTextSecondary; }
            });
        });
        PanelContent.Children.Add(CreateCard(controlStack));

        var audioStack = new WrapPanel();
        var devices = AudioController.GetPlaybackDevices(AudioSwitcher.AudioApi.DeviceState.Active).Take(4);
        foreach (var d in devices)
        {
            bool isDefault = d.Id == defAudio.Id;
            var btn = new Button { Content = d.Name.Length > 8 ? d.Name.Substring(0, 8) + "..." : d.Name, Background = isDefault ? ColorAccent : new SolidColorBrush(Color.FromRgb(50, 50, 50)), Foreground = Brushes.White, Padding = new Thickness(10, 5, 10, 5), BorderThickness = new Thickness(0), Margin = new Thickness(0, 0, 10, 10), Cursor = Cursors.Hand };
            btn.Click += (_, _) => { d.SetAsDefault(); LoadSettingsPanel(); };
            audioStack.Children.Add(btn);
        }
        PanelContent.Children.Add(new TextBlock { Text = "音频输出设备", Foreground = ColorTextSecondary, FontSize = 12, Margin = new Thickness(0, 5, 0, 5) });
        PanelContent.Children.Add(CreateCard(audioStack));

        var toolsStack = new StackPanel { Orientation = Orientation.Horizontal };
        toolsStack.Children.Add(CreateToolButton("CMD", "cmd.exe"));
        toolsStack.Children.Add(CreateToolButton("PS", "powershell.exe"));
        toolsStack.Children.Add(CreateToolButton("设置", "ms-settings:"));
        PanelContent.Children.Add(CreateCard(toolsStack));

        var powerStack = new StackPanel { Orientation = Orientation.Horizontal };
        var btnShutdown = new Button { Content = "关机", Background = new SolidColorBrush(Color.FromRgb(220, 50, 50)), Foreground = Brushes.White, Padding = new Thickness(20, 8, 20, 8), BorderThickness = new Thickness(0), Margin = new Thickness(0, 0, 10, 0), Cursor = Cursors.Hand };
        btnShutdown.Click += (_, _) => Process.Start("shutdown", "/s /t 0");
        var btnRestart = new Button { Content = "重启", Background = new SolidColorBrush(Color.FromRgb(220, 150, 50)), Foreground = Brushes.White, Padding = new Thickness(20, 8, 20, 8), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
        btnRestart.Click += (_, _) => Process.Start("shutdown", "/r /t 0");
        powerStack.Children.Add(btnShutdown); powerStack.Children.Add(btnRestart);
        PanelContent.Children.Add(powerStack);
    }

    private Button CreateToolButton(string label, string path)
    {
        var btn = new Button { Content = label, Background = new SolidColorBrush(Color.FromRgb(50, 50, 50)), Foreground = Brushes.White, Padding = new Thickness(12, 8, 12, 8), BorderThickness = new Thickness(0), Margin = new Thickness(0, 0, 10, 0), Cursor = Cursors.Hand };
        btn.Click += (_, _) => Process.Start(new ProcessStartInfo(path) { UseShellExecute = true, Verb = path.EndsWith(".exe") ? "runas" : "" });
        return btn;
    }

    private int GetBrightness()
    {
        try
        {
            using var searcher = new ManagementObjectSearcher("root\\WMI", "SELECT * FROM WmiMonitorBrightness");
            foreach (ManagementObject obj in searcher.Get()) return Convert.ToInt32(obj["CurrentBrightness"]);
        }
        catch { }
        return -1;
    }

    private void SetBrightness(int val)
    {
        try
        {
            using var searcher = new ManagementObjectSearcher("root\\WMI", "SELECT * FROM WmiMonitorBrightnessMethods");
            foreach (ManagementObject obj in searcher.Get()) obj.InvokeMethod("WmiSetBrightness", new object[] { 1, val });
        }
        catch { }
    }

    private async Task LoadRadioPanel(RadioKind kind)
    {
        int currentGen = _panelGeneration;
        var radios = await Radio.GetRadiosAsync();
        if (currentGen != _panelGeneration) return;
        var radio = radios.FirstOrDefault(r => r.Kind == kind);
        if (radio == null) { PanelContent.Children.Add(new TextBlock { Text = "未找到此硬件", Foreground = ColorTextSecondary }); return; }

        bool isOn = radio.State == RadioState.On;
        var headerStack = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 15) };
        headerStack.Children.Add(new TextBlock { Text = isOn ? "已开启" : "已关闭", Foreground = isOn ? ColorAccent : ColorTextSecondary, VerticalAlignment = VerticalAlignment.Center, Margin = new Thickness(0, 0, 15, 0), FontSize = 14 });
        var toggleBtn = new Button { Content = isOn ? "关闭" : "开启", Background = new SolidColorBrush(Color.FromRgb(50, 50, 50)), Foreground = Brushes.White, Padding = new Thickness(15, 5, 15, 5), BorderThickness = new Thickness(0), Cursor = Cursors.Hand };
        toggleBtn.Click += async (_, _) => {
            toggleBtn.IsEnabled = false;
            bool currentlyOn = radio.State == RadioState.On;
            var result = await radio.SetStateAsync(currentlyOn ? RadioState.Off : RadioState.On);
            if (result == RadioAccessStatus.Allowed)
            {
                isOn = !currentlyOn;
                ((TextBlock)headerStack.Children[0]).Text = isOn ? "已开启" : "已关闭";
                ((TextBlock)headerStack.Children[0]).Foreground = isOn ? ColorAccent : ColorTextSecondary;
                toggleBtn.Content = isOn ? "关闭" : "开启";
            }
            toggleBtn.IsEnabled = true;
        };
        headerStack.Children.Add(toggleBtn);
        PanelContent.Children.Add(CreateCard(headerStack));
        if (!isOn) return;

        var listStack = new StackPanel();
        listStack.Children.Add(new TextBlock { Text = "正在扫描...", Foreground = ColorTextSecondary, FontSize = 12 });
        PanelContent.Children.Add(listStack);

        if (kind == RadioKind.WiFi)
        {
            try
            {
                var adapters = await WiFiAdapter.FindAllAdaptersAsync();
                if (currentGen != _panelGeneration) return;
                if (adapters.Count > 0)
                {
                    var adapter = adapters[0];
                    await adapter.ScanAsync();
                    if (currentGen != _panelGeneration) return;
                    listStack.Children.Clear();
                    var connectedProfile = await adapter.NetworkAdapter.GetConnectedProfileAsync();
                    var networks = adapter.NetworkReport.AvailableNetworks.OrderByDescending(n => n.NetworkRssiInDecibelMilliwatts);
                    foreach (var net in networks.Take(5))
                    {
                        bool isConnected = connectedProfile != null && connectedProfile.ProfileName == net.Ssid;
                        var btn = CreateListItemButton(isConnected ? $"📶 {net.Ssid} (已连接)" : $"📶 {net.Ssid}", net.Ssid);
                        btn.Click += async (_, _) => {
                            try
                            {
                                if (isConnected) adapter.Disconnect();
                                else
                                {
                                    var result = await adapter.ConnectAsync(net, WiFiReconnectionKind.Automatic);
                                    if (result.ConnectionStatus != WiFiConnectionStatus.Success) MessageBox.Show("连接失败。该网络可能需要密码。", "提示");
                                }
                                OpenPanel("WiFi");
                            }
                            catch (Exception ex) { MessageBox.Show($"WiFi 操作失败: {ex.Message}"); }
                        };
                        listStack.Children.Add(btn);
                    }
                    if (!networks.Any()) listStack.Children.Add(new TextBlock { Text = "未找到附近的 WiFi", Foreground = ColorTextSecondary });
                    var netSettingsBtn = CreateListItemButton("⚙️ 网络连接 (控制面板)", "");
                    netSettingsBtn.Click += (_, _) => Process.Start(new ProcessStartInfo("ncpa.cpl") { UseShellExecute = true });
                    listStack.Children.Add(netSettingsBtn);
                }
                else listStack.Children.Add(new TextBlock { Text = "未找到 WiFi 适配器", Foreground = ColorTextSecondary });
            }
            catch { listStack.Children.Add(new TextBlock { Text = "扫描失败，请确保系统定位已开启", Foreground = ColorTextSecondary }); }
        }
        else
        {
            try
            {
                var devices = await DeviceInformation.FindAllAsync(BluetoothDevice.GetDeviceSelectorFromPairingState(true));
                if (currentGen != _panelGeneration) return;
                listStack.Children.Clear();
                if (!devices.Any()) listStack.Children.Add(new TextBlock { Text = "没有已配对的蓝牙设备", Foreground = ColorTextSecondary });
                foreach (var dev in devices.Take(5))
                {
                    var btn = CreateListItemButton($"🔗 {dev.Name} (点击断开)", dev.Name);
                    btn.Click += async (_, _) => {
                        try
                        {
                            var result = await dev.Pairing.UnpairAsync();
                            if (result.Status == DeviceUnpairingResultStatus.Unpaired) OpenPanel("蓝牙");
                        }
                        catch { MessageBox.Show("取消配对失败"); }
                    };
                    listStack.Children.Add(btn);
                }
            }
            catch { listStack.Children.Add(new TextBlock { Text = "获取蓝牙设备失败", Foreground = ColorTextSecondary }); }
        }
    }

    private async Task LoadNotificationPanel()
    {
        int currentGen = _panelGeneration;
        var listener = UserNotificationListener.Current;
        if (listener.GetAccessStatus() != UserNotificationListenerAccessStatus.Allowed) { PanelContent.Children.Add(new TextBlock { Text = "没有权限", Foreground = ColorTextSecondary }); return; }

        IReadOnlyList<UserNotification> notifications;
        try
        {
            notifications = await listener.GetNotificationsAsync(NotificationKinds.Toast);
        }
        catch
        {
            PanelContent.Children.Add(new TextBlock { Text = "无法读取系统通知", Foreground = ColorTextSecondary });
            return;
        }

        if (currentGen != _panelGeneration) return;
        if (!notifications.Any()) { PanelContent.Children.Add(new TextBlock { Text = "暂无通知", Foreground = ColorTextSecondary }); return; }

        int count = 0;
        foreach (var n in notifications)
        {
            if (count >= 5) break;

            try
            {
                string title = "";
                string body = "";
                string appName = "应用";

                try
                {
                    var textBinding = n.Notification.Visual.GetBinding(KnownNotificationBindings.ToastGeneric);
                    if (textBinding != null)
                    {
                        var textElements = textBinding.GetTextElements();
                        if (textElements != null)
                        {
                            title = textElements.Count > 0 ? textElements[0].Text : "";
                            body = textElements.Count > 1 ? textElements[1].Text : "";
                        }
                    }
                }
                catch { }

                try
                {
                    if (n.AppInfo != null && n.AppInfo.DisplayInfo != null)
                    {
                        appName = n.AppInfo.DisplayInfo.DisplayName;
                    }
                }
                catch { }

                string fullText = $"{title} {body}".Replace("\n", " ").Trim();
                if (string.IsNullOrWhiteSpace(fullText)) continue;
                if (fullText.Length > 20) fullText = fullText.Substring(0, 20) + "...";

                var itemStack = new StackPanel();
                var headerGrid = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(0, 0, 0, 5) };

                try
                {
                    var logo = n.AppInfo?.DisplayInfo?.GetLogo(new Windows.Foundation.Size(16, 16));
                    if (logo != null)
                    {
                        using var stream = await logo.OpenReadAsync();
                        using var ms = new MemoryStream();
                        await stream.AsStreamForRead().CopyToAsync(ms);
                        ms.Position = 0;

                        var bmp = new BitmapImage();
                        bmp.BeginInit();
                        bmp.StreamSource = ms;
                        bmp.CacheOption = BitmapCacheOption.OnLoad;
                        bmp.EndInit();
                        bmp.Freeze();

                        headerGrid.Children.Add(new Image { Source = bmp, Width = 16, Height = 16, Margin = new Thickness(0, 0, 8, 0) });
                    }
                }
                catch { }

                headerGrid.Children.Add(new TextBlock { Text = appName, Foreground = ColorTextSecondary, FontSize = 12, VerticalAlignment = VerticalAlignment.Center });
                itemStack.Children.Add(headerGrid);
                itemStack.Children.Add(new TextBlock { Text = fullText, Foreground = ColorTextPrimary, FontSize = 14, TextWrapping = TextWrapping.Wrap });
                PanelContent.Children.Add(CreateCard(itemStack));
                count++;
            }
            catch
            {
                continue;
            }
        }
    }

    private void GoL1()
    {
        _state = State.L1;
        _closeTimer.Stop();
        AnimateTo(L1W, GetL1H(), 400, 1100);
    }

    private void AnimateTo(double w, double h, double widthMs, double heightMs)
    {
        var ease = new BackEase { EasingMode = EasingMode.EaseOut, Amplitude = 0.15 };

        var wAnim = new DoubleAnimation(w, TimeSpan.FromMilliseconds(widthMs)) { EasingFunction = ease, FillBehavior = FillBehavior.Stop };
        wAnim.Completed += (s, e) => { BeginAnimation(WidthProperty, null); Width = w; };
        BeginAnimation(WidthProperty, wAnim);

        var hAnim = new DoubleAnimation(h, TimeSpan.FromMilliseconds(heightMs)) { EasingFunction = ease, FillBehavior = FillBehavior.Stop };
        hAnim.Completed += (s, e) => { BeginAnimation(HeightProperty, null); Height = h; };
        BeginAnimation(HeightProperty, hAnim);
    }
}