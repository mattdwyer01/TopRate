@echo off
setlocal enabledelayedexpansion
cd /d "%~dp0"

echo === TopRate HTML Deploy (fast, no data fetch) ===
echo.

REM Sync with remote (stash/pull/pop), commit the template, rebuild HTML from
REM the EXISTING csv (skips the slow API fetch), push. For HTML/CSS template
REM changes only. Use deploy.bat when you need fresh data.

echo [1/3] Sync + commit template...
set STASHED=0
for /f %%i in ('git diff --name-only') do set STASHED=1
for /f %%i in ('git diff --cached --name-only') do set STASHED=1
if "!STASHED!"=="1" git stash push -m "html deploy auto-stash"
git pull --rebase
if errorlevel 1 ( echo ERROR: pull failed. If you stashed: git stash pop & pause & exit /b 1 )
if "!STASHED!"=="1" (
    git stash pop
    if errorlevel 1 ( echo WARNING: stash conflicts - resolve manually. & pause & exit /b 1 )
)
if exist toprate_html_v3.py git add toprate_html_v3.py
if exist deploy_html.bat git add deploy_html.bat
set HAS_STAGED=
for /f %%i in ('git diff --cached --name-only') do set HAS_STAGED=1
if defined HAS_STAGED (
    git commit -m "HTML template update"
    git push
    if errorlevel 1 ( echo ERROR: push failed. & pause & exit /b 1 )
    echo   Pushed template.
) else (
    echo   No template changes.
)

echo.
echo [2/3] Rebuild HTML from existing data (no fetch)...
python toprate_daily.py --rebuild-only --publish
if errorlevel 1 ( echo ERROR: rebuild failed. & pause & exit /b 1 )

echo.
echo [3/3] Commit rebuilt HTML...
if exist toprate_live.html git add toprate_live.html
set HAS_HTML=
for /f %%i in ('git diff --cached --name-only') do set HAS_HTML=1
if defined HAS_HTML (
    git commit -m "Rebuild HTML"
    git push
    echo   HTML pushed.
) else (
    echo   No HTML change.
)

echo.
echo === Done (fast HTML deploy) ===
echo Open: https://mattdwyer01.github.io/TopRate/toprate_live.html
echo Hit Ctrl+Shift+R to bypass cache
echo.
pause
