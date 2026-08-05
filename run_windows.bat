@echo off
setlocal
cd /d "%~dp0"

if not exist ".venv\Scripts\python.exe" (
    echo Creating Python virtual environment...
    py -3.12 -m venv .venv 2>nul
    if errorlevel 1 py -3 -m venv .venv
    if errorlevel 1 (
        echo.
        echo Could not create the virtual environment. Install 64-bit Python 3.12 or newer.
        pause
        exit /b 1
    )
)

call ".venv\Scripts\activate.bat"
python -m pip install --upgrade pip
if errorlevel 1 goto :failed
python -m pip install -r requirements.txt
if errorlevel 1 goto :failed
python canelevation_terrain_exporter.py
exit /b %errorlevel%

:failed
echo.
echo Dependency installation failed. Copy the output above when asking for help.
pause
exit /b 1
