@echo off
setlocal enabledelayedexpansion
cd /d "%~dp0"

echo === TopRate Deploy ===
echo.

REM ─────────────────────────────────────────────────────────
REM Step 1: Stash ONLY tracked file changes (no untracked)
REM   This prevents the bat from stashing itself.
REM ─────────────────────────────────────────────────────────
echo [1/5] Checking for tracked file changes...
set HAS_CHANGES=
for /f %%i in ('git diff --name-only') do set HAS_CHANGES=1
for /f %%i in ('git diff --cached --name-only') do set HAS_CHANGES=1

if defined HAS_CHANGES (
    echo   Stashing tracked changes...
    REM Note: NO -u flag, so untracked files including this bat stay put
    git stash push -m "deploy.bat auto-stash"
    set STASHED=1
) else (
    echo   No changes to stash.
    set STASHED=0
)

REM ─────────────────────────────────────────────────────────
REM Step 2: Pull
REM ─────────────────────────────────────────────────────────
echo.
echo [2/5] Pulling from remote...
git pull --rebase
if errorlevel 1 (
    echo ERROR: pull failed.
    if "!STASHED!"=="1" echo To recover changes: git stash pop
    pause
    exit /b 1
)

REM ─────────────────────────────────────────────────────────
REM Step 3: Pop stash
REM ─────────────────────────────────────────────────────────
if "!STASHED!"=="1" (
    echo.
    echo   Restoring stashed changes...
    git stash pop
    if errorlevel 1 (
        echo WARNING: stash pop conflicts. Resolve manually.
        pause
        exit /b 1
    )
)

REM ─────────────────────────────────────────────────────────
REM Step 4: Stage and push code/config files
REM ─────────────────────────────────────────────────────────
echo.
echo [3/5] Committing changes...
if exist toprate_html_v3.py git add toprate_html_v3.py
if exist toprate_daily.py git add toprate_daily.py
if exist .gitattributes git add .gitattributes
if exist deploy.bat git add deploy.bat
if exist .github\workflows\daily.yml git add .github\workflows\daily.yml

set HAS_STAGED=
for /f %%i in ('git diff --cached --name-only') do set HAS_STAGED=1

if defined HAS_STAGED (
    set /p MSG="Commit message [Update dashboard]: "
    if "!MSG!"=="" set MSG=Update dashboard
    git commit -m "!MSG!"
    git push
    if errorlevel 1 (
        echo ERROR: push failed.
        pause
        exit /b 1
    )
    echo   Pushed.
) else (
    echo   Nothing to commit.
)

REM ─────────────────────────────────────────────────────────
REM Step 5: Refetch API data
REM ─────────────────────────────────────────────────────────
echo.
echo [4/5] Refetching API data...
python toprate_daily.py
if errorlevel 1 (
    echo ERROR: data fetch failed.
    pause
    exit /b 1
)

REM ─────────────────────────────────────────────────────────
REM Step 6: Republish HTML
REM ─────────────────────────────────────────────────────────
echo.
echo [5/5] Publishing HTML...
python toprate_daily.py --publish
if errorlevel 1 (
    echo ERROR: publish failed.
    pause
    exit /b 1
)

REM ─────────────────────────────────────────────────────────
REM Step 7: Commit fresh data + HTML
REM ─────────────────────────────────────────────────────────
echo.
echo   Committing data updates...
if exist toprate_runners.csv git add toprate_runners.csv
if exist toprate_model_picks.csv git add toprate_model_picks.csv
if exist toprate_price_history.csv git add toprate_price_history.csv
if exist toprate_live.html git add toprate_live.html

set HAS_DATA=
for /f %%i in ('git diff --cached --name-only') do set HAS_DATA=1

if defined HAS_DATA (
    git commit -m "Data update"
    git push
    echo   Data pushed.
) else (
    echo   No data changes.
)

echo.
echo === Done ===
echo Open: https://mattdwyer01.github.io/TopRate/toprate_live.html
echo Hit Ctrl+Shift+R to bypass cache
echo.
pause
