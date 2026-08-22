@echo off
setlocal enabledelayedexpansion
cd /d "%~dp0"

echo === TopRate Frontend Deploy (rebuild dashboard, no data fetch) ===
echo.

REM Sync with remote (stash/pull/pop), commit frontend source changes, build
REM the frontend/ React+Vite app and publish it as toprate_live.html, push.
REM For dashboard UI changes only. Use deploy.bat when you need fresh data.
REM
REM toprate_live.html is a static build - it fetches toprate_data.json at
REM runtime, so it only needs rebuilding when frontend/src changes, not on
REM every data refresh (the daily run and price-refresh workflows leave it
REM alone; see toprate_daily.py's rebuild_html()).

echo [1/3] Sync + commit frontend source...
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
if exist frontend\src git add frontend\src
if exist frontend\public git add frontend\public
if exist frontend\package.json git add frontend\package.json
if exist frontend\package-lock.json git add frontend\package-lock.json
if exist frontend\vite.config.ts git add frontend\vite.config.ts
if exist deploy_html.bat git add deploy_html.bat
set HAS_STAGED=
for /f %%i in ('git diff --cached --name-only') do set HAS_STAGED=1
if defined HAS_STAGED (
    git commit -m "Frontend update"
    git push
    if errorlevel 1 ( echo ERROR: push failed. & pause & exit /b 1 )
    echo   Pushed frontend source.
) else (
    echo   No frontend source changes.
)

echo.
echo [2/3] Building frontend...
pushd frontend
call npm install
if errorlevel 1 ( echo ERROR: npm install failed. & popd & pause & exit /b 1 )
call npm run build
if errorlevel 1 ( echo ERROR: frontend build failed. & popd & pause & exit /b 1 )
popd
copy /Y frontend\dist\index.html toprate_live.html
if exist frontend\dist\favicon.svg copy /Y frontend\dist\favicon.svg favicon.svg

echo.
echo [3/3] Commit rebuilt dashboard...
if exist toprate_live.html git add toprate_live.html
if exist favicon.svg git add favicon.svg
set HAS_HTML=
for /f %%i in ('git diff --cached --name-only') do set HAS_HTML=1
if defined HAS_HTML (
    git commit -m "Rebuild dashboard"
    git push
    echo   Dashboard pushed.
) else (
    echo   No dashboard change.
)

echo.
echo === Done (frontend deploy) ===
echo Open: https://mattdwyer01.github.io/TopRate/toprate_live.html
echo Hit Ctrl+Shift+R to bypass cache
echo.
pause
