#include <io.h>
#include <process.h>
#include <stdint.h>
#include <stdio.h>
#include <windows.h>

// THis file exists to avoid clashes between windows.h and idris_rts.h
//

int win_fpoll(FILE *f) {
    HANDLE wh = (HANDLE)_get_osfhandle(_fileno(f));
    if (wh == INVALID_HANDLE_VALUE) {
        return -1;
    }
    DWORD ret = WaitForSingleObject(wh, 1000);
    // Imitate the return values of select()
    if (ret == WAIT_OBJECT_0)
        return 1;
    if (ret == WAIT_TIMEOUT)
        return 0;
    return -1;
}

int widen_utf8(const char *filename_utf8, LPWSTR *filename_w) {
    int num_chars = MultiByteToWideChar(CP_UTF8, 0, filename_utf8, -1, 0, 0);
    int size = sizeof(WCHAR);
    *filename_w = (LPWSTR)malloc(size * num_chars);
    MultiByteToWideChar(CP_UTF8, 0, filename_utf8, -1, *filename_w, num_chars);
    return num_chars;
}

FILE *win32_u8fopen(const char *path, const char *mode) {
    LPWSTR wpath, wmode;
    widen_utf8(path, &wpath);
    widen_utf8(mode, &wmode);
    FILE *f = _wfopen(wpath, wmode);
    free(wpath);
    free(wmode);
    return f;
}

FILE *win32_u8popen(const char *path, const char *mode) {
    LPWSTR wpath, wmode;
    widen_utf8(path, &wpath);
    widen_utf8(mode, &wmode);
    FILE *f = _wpopen(wpath, wmode);
    free(wpath);
    free(wmode);
    return f;
}

void win32_gettime(int64_t *sec, int64_t *nsec) {
    FILETIME ft;
#ifdef _OLD_WIN
    GetSystemTimeAsFileTime(&ft);
#else
    // For Windows NT 6.2 or higher
    GetSystemTimePreciseAsFileTime(&ft);
#endif
    ULARGE_INTEGER t;
    t.HighPart = ft.dwHighDateTime;
    t.LowPart = ft.dwLowDateTime;

    *nsec = (t.QuadPart % 10000000) * 100;
    *sec = t.QuadPart / 10000000;
    *sec -= 11644473600; // LDAP epoch to Unix epoch
}

void win32_sleep(int ms) {
    Sleep(ms);
}

int win32_modenv(const char *name, const char *value, int overwrite) {
    if (!overwrite && getenv(name))
        return 0;
    return _putenv_s(name, value);
}

int win32_getErrno() {
    return GetLastError();
}

int win32_getPID() {
    return _getpid();
}

typedef BOOL(WINAPI *LPFN_GLPI)(PSYSTEM_LOGICAL_PROCESSOR_INFORMATION, PDWORD);

long win32_getNProcessors() {
    // largely taken from
    // https://docs.microsoft.com/en-us/windows/win32/api/sysinfoapi/nf-sysinfoapi-getlogicalprocessorinformation

    BOOL done = FALSE;
    long nPhysicalProcessors = 0;
    long nSMTProcessors = 0;

    // length of array for storing the information structs
    DWORD returnLength = 0;
    // structs for storing the information
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION buffer = NULL;
    PSYSTEM_LOGICAL_PROCESSOR_INFORMATION ptr = NULL;

    // shortcut to a function (?)
    LPFN_GLPI glpi;
    glpi = (LPFN_GLPI)GetProcAddress(GetModuleHandle(TEXT("kernel32")),
                                     "GetLogicalProcessorInformation");
    // to keep track of whether we're at the end of the array
    DWORD byteOffset = 0;

    // repeatedly try to malloc and retrieve the information until we have a
    // large enough array of information structs, or we fail to malloc
    while (!done) {
        DWORD rc = glpi(buffer, &returnLength);
        if (rc == FALSE) {
            if (GetLastError() == ERROR_INSUFFICIENT_BUFFER) {
                // this will happen initially since buffer = NULL and we need to
                // somehow retrieve the required size

                if (buffer) {
                    free(buffer);
                }

                buffer =
                    (PSYSTEM_LOGICAL_PROCESSOR_INFORMATION)malloc(returnLength);

                if (NULL == buffer) {
                    // memory allocation error
                    return -1;
                }

            } else {
                // something else went wrong
                return -1;
            }
        } else {
            done = TRUE;
        }
    }

    ptr = buffer;

    while ((byteOffset + sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION)) <=
           returnLength) {
        // if we have a processor core, count the processors
        if (ptr->Relationship == RelationProcessorCore) {
            nPhysicalProcessors++;

            // if we have an SMT-enabled CPU, we need to count the virtual
            // cores as well
            DWORD lshift = sizeof(ULONG_PTR) * 8 - 1;
            ULONG_PTR bitTest = (ULONG_PTR)1 << lshift;
            DWORD i;
            for (i = 0; i <= lshift; ++i) {
                // count the bit if it is set
                nSMTProcessors += ((ptr->ProcessorMask & bitTest) ? 1 : 0);
                // move the test to the next bit
                bitTest /= 2;
            }
        }
        // move to next info element
        byteOffset += sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION);
        ptr++;
    }

    // return the larger number of physical vs SMT cores
    // (if this bothers you, overhaul this implementation with a solution that
    // distinguishes between types of cores on _both_ *NIX and Windows!)
    return nPhysicalProcessors == nSMTProcessors ? nPhysicalProcessors
                                                 : nSMTProcessors;
}
