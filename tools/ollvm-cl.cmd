@echo off
REM Thin shim — delegates to ollvm-cl.py to avoid CMD splitting = in flags.
python "%~dp0ollvm-cl.py" %*
exit /b %ERRORLEVEL%
