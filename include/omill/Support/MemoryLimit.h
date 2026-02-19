#pragma once

/// Set a process-wide memory limit using Windows Job Objects.
/// Call early in main() before heavy allocations.
/// No-op on non-Windows platforms.

#ifdef _WIN32

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif

// Forward-declare the Win32 APIs we need to avoid pulling in <windows.h>
// (which conflicts with Ghidra's CHAR typedefs in sleigh/remill builds).
extern "C" {

typedef unsigned long DWORD;
typedef int BOOL;
typedef void *HANDLE;
typedef struct _SECURITY_ATTRIBUTES *LPSECURITY_ATTRIBUTES;

HANDLE __stdcall CreateJobObjectA(LPSECURITY_ATTRIBUTES, const char *);
BOOL __stdcall SetInformationJobObject(HANDLE, int, void *, DWORD);
BOOL __stdcall AssignProcessToJobObject(HANDLE, HANDLE);
HANDLE __stdcall GetCurrentProcess();
BOOL __stdcall CloseHandle(HANDLE);

// JOBOBJECT_EXTENDED_LIMIT_INFORMATION layout (x64).
#pragma pack(push, 8)
struct OMILL_JOBOBJECT_BASIC_LIMIT_INFORMATION {
  long long PerProcessUserTimeLimit;
  long long PerJobUserTimeLimit;
  DWORD LimitFlags;
  size_t MinimumWorkingSetSize;
  size_t MaximumWorkingSetSize;
  DWORD ActiveProcessLimit;
  unsigned long long Affinity;
  DWORD PriorityClass;
  DWORD SchedulingClass;
};

struct OMILL_IO_COUNTERS {
  unsigned long long ReadOperationCount;
  unsigned long long WriteOperationCount;
  unsigned long long OtherOperationCount;
  unsigned long long ReadTransferCount;
  unsigned long long WriteTransferCount;
  unsigned long long OtherTransferCount;
};

struct OMILL_JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
  OMILL_JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
  OMILL_IO_COUNTERS IoInfo;
  size_t ProcessMemoryLimit;
  size_t JobMemoryLimit;
  size_t PeakProcessMemoryUsed;
  size_t PeakJobMemoryUsed;
};
#pragma pack(pop)

}  // extern "C"

namespace omill {

/// Set a per-process memory limit (bytes).  Returns true on success.
inline bool setProcessMemoryLimit(size_t limit_bytes) {
  constexpr int JobObjectExtendedLimitInformation = 9;
  constexpr DWORD JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x00000100;

  HANDLE job = CreateJobObjectA(nullptr, nullptr);
  if (!job) return false;

  OMILL_JOBOBJECT_EXTENDED_LIMIT_INFORMATION jeli{};
  jeli.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_PROCESS_MEMORY;
  jeli.ProcessMemoryLimit = limit_bytes;

  if (!SetInformationJobObject(job, JobObjectExtendedLimitInformation,
                               &jeli, sizeof(jeli))) {
    CloseHandle(job);
    return false;
  }

  if (!AssignProcessToJobObject(job, GetCurrentProcess())) {
    CloseHandle(job);
    return false;
  }

  // Handle kept alive; OS enforces the limit while the process lives.
  return true;
}

}  // namespace omill

#else  // !_WIN32

namespace omill {
inline bool setProcessMemoryLimit(size_t) { return true; }
}  // namespace omill

#endif
