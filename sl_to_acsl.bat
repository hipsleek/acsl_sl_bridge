@echo off
setlocal EnableDelayedExpansion

set USE_GUI=0

REM -----------------------------
REM Parse flags
REM -----------------------------
if "%~1"=="--gui" (
  set USE_GUI=1
  shift
)

REM -----------------------------
REM Input handling
REM -----------------------------
if not "%~1"=="" (
  set INPUT=%~1
) else (
  set INPUT=%TEMP%\sl_input_%RANDOM%.c
  more > "%INPUT%"
)

REM -----------------------------
REM Run SL -> ACSL translator
REM -----------------------------
dune exec ./src/main.exe -- "%INPUT%"
if errorlevel 1 (
  echo SL to ACSL translation failed
  exit /b 1
)

REM -----------------------------
REM Compute ACSL output name
REM -----------------------------
for %%F in ("%INPUT%") do (
  set DIR=%%~dpF
  set STEM=%%~nF
)

set ACSL_FILE=%DIR%%STEM%_acsl.c

if not exist "%ACSL_FILE%" (
  echo Error: ACSL output not found: %ACSL_FILE%
  exit /b 1
)

REM -----------------------------
REM Run Frama-C
REM -----------------------------
if "%USE_GUI%"=="1" (
  frama-c-gui -wp -wp-no-simpl -wp-no-let "%ACSL_FILE%"
) else (
  frama-c -wp -wp-no-simpl -wp-no-let "%ACSL_FILE%"
)
