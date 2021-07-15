#ifdef _WIN32

#include <windows.h>

#ifndef ENABLE_VIRTUAL_TERMINAL_PROCESSING
#define ENABLE_VIRTUAL_TERMINAL_PROCESSING 0x0004
#endif

void idris2_setupTerm() {
    HANDLE stdout_handle = GetStdHandle(STD_OUTPUT_HANDLE);
    DWORD outmode = 0;
    GetConsoleMode(stdout_handle, &outmode);
    outmode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
    SetConsoleMode(stdout_handle, outmode);
}

int idris2_getTermCols() {
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
    return (int)csbi.srWindow.Right - csbi.srWindow.Left + 1;
}

int idris2_getTermLines() {
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
    return (int)csbi.srWindow.Bottom - csbi.srWindow.Top + 1;
}

#else

#include <sys/ioctl.h>

void idris2_setupTerm() {
    // NOTE: Currently not needed for non windows systems
}

int idris2_getTermCols() {
    struct winsize ts;
    ioctl(0, TIOCGWINSZ, &ts);
    return (int)ts.ws_col;
}

int idris2_getTermLines() {
    struct winsize ts;
    ioctl(0, TIOCGWINSZ, &ts);
    return (int)ts.ws_row;
}

#endif
