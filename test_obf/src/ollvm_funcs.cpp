#define EXPORT extern "C" __declspec(dllexport)

// CFF target: multi-way branching.
EXPORT int ollvm_branch(int x) {
    if (x > 10) return x * 2;
    else if (x > 0) return x + 5;
    else return -x;
}

// MBA target: arithmetic expressions.
EXPORT int ollvm_arithmetic(int a, int b) {
    return (a + b) ^ (a - b);
}

// String encryption target: inline string copy.
EXPORT int ollvm_copy_greeting(char *buf, int bufsize) {
    const char msg[] = "OLLVM Test String!";
    int i = 0;
    while (msg[i] && i < bufsize - 1) { buf[i] = msg[i]; i++; }
    buf[i] = '\0';
    return i;
}

// CFF + loop target.
EXPORT int ollvm_loop_sum(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) sum += i;
    return sum;
}
