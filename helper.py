MOD = int(1e9 + 7)

def modpow(x, p):
    if p == 0:
        return 1
    if p == 1:
        return x % MOD
    ans = modpow(x, p // 2)
    ans = (ans * ans) % MOD
    if p % 2 == 1:
        ans = (ans * x) % MOD
    return ans