#ifdef LOCAL
#include "bits/debug.h"
#include "bits/stdc++.h"
#else
#define dbg(...) 42
#include <bits/stdc++.h>
#endif

using namespace std;
using ll = long long;
using ul = unsigned long;
using ull = unsigned long long;
using ld = long double;
using vi = vector<int>;
using vvi = vector<vi>;
using vll = vector<ll>;
using pll = pair<ll, ll>;
using vpll = vector<pair<ll, ll>>;
using qi = queue<int>;
using pii = pair<int, int>;
using di = deque<int>;
using dpi = deque<pii>;
using vpi = vector<pii>;
using tii = tuple<int, int, int>;
using vti = vector<tii>;
using qpi = queue<pii>;
using qti = queue<tii>;
using vc = vector<char>;
using si = unordered_set<int>;
using mosi = multiset<int>;
#define lso(S) ((S) & -(S))
const int MOD = 998244353; // 1e9 + 7;
const int F = 1e5;
const ll INF = 2e18;
int dr[] = {0, 1, -1, 0, 1, -1, 1, -1};
int dc[] = {1, 0, 0, -1, 1, -1, -1, 1};

/*
 * Algebra/Fundamentals
 */ 
ll modexp(ll a, ll b, ll mod = MOD){
    a %= mod; ll ans = 1;
    while (b){
        if (b & 1){
            ans = (ans * a) % mod;
        }
        a = (a * a) % mod;
        b = b >> 1;
    }
    return ans;
}

ll extgcd(ll a, ll b, ll& x, ll& y){
    // compute g = gcd(a, b), and 
    // x, y s.t. ax + by = g
    if (b == 0){
        x = 1; y = 0;
        return a;
    }
    ll x1, y1;
    ll d = extgcd(b, a % b, x1, y1);
    x = y1;
    y = x1 - y1 * (a / b);
    return d;
}

ll modinv(ll a, ll mod = MOD){
    // ax + mod * y = 1 ==> ax = 1 (mod mod)
    ll x, y;
    extgcd(a, mod, x, y);
    return x;
}

pll diophantine(ll a, ll b, ll c){
    /* find an integer solution for 
     * ax + by = c. Only exists if
     * c % g == 0 obviously.
     */ 
    ll g = gcd(a, b);
    ll x = (c / g) * modinv(a / g, b / g);
    ll y = (c - a * x) / b;
    // all solutions are of the form:
    // (x + k * (b / g), y - k * (a / g))
    return {x, y};
}

struct fibonacci{
    vll fib{0, 1, 1};
    void pre(const int maxn = F){
        for (int i = 0; i < maxn; ++i){
            fib.push_back(fib[i + 1] + fib[i + 2]);
        }
    }
    pll nth_fib(int n){
        /* Here we take advantage of 
        F(2k + 1) = F(k + 1)^2 + F(k)^2
        F(2k) = F(k)(F(k + 1) + F(k - 1))
        which are obvious from matrix exponent
        this is O(log(n))
        */
        if (n == 0) return {0ll, 1ll};
        
        auto [h, hp] = nth_fib(n >> 1);
        ll c = h * (2 * hp - h);
        ll d = h * h + hp * hp;
        return (n & 1) ? make_pair(d, c + d) : make_pair(c, d);
    }
};

vi invs(const vi &a, int m = MOD) { // finds the modinv of each element in a
    // calculates the inv of denominator. Then the inv of xi is
    // product[:i] * denominator_inv * product a[i + 1:]
    int n = a.size();
    if (n == 0) return {};
    vi b(n);
    ll v = 1;
    for (int i = 0; i != n; ++i) {
        b[i] = v;
        v = v * a[i] % m;
    }
    ll x, y;
    extgcd(v, m, x, y);
    x = (x % m + m) % m;
    for (int i = n - 1; i >= 0; --i) {
        b[i] = x * b[i] % m;
        x = x * a[i] % m;
    }
    return b;
}

struct factorial {
    const int MAXN = 5e6;
    vll fact{};
    vll inv{};

    ll extgcd(ll a, ll b, ll& x, ll& y){
        // compute g = gcd(a, b), and 
        // x, y s.t. ax + by = g
        if (b == 0){
            x = 1; y = 0;
            return a;
        }
        ll x1, y1;
        ll d = extgcd(b, a % b, x1, y1);
        x = y1;
        y = x1 - y1 * (a / b);
        return d;
    }
    ll modinv(ll val){
        ll x, y;
        extgcd(val, MOD, x, y);
        return x;
    }
    void invs() {
        inv.resize(MAXN + 1);
        ll v = 1;
        for (int i = 0; i < MAXN; ++i) {
            inv[i] = v;
            v = v * fact[i] % MOD;
        }
        ll x, y;
        extgcd(v, MOD, x, y);
        if (x < 0) x += MOD;
        for (int i = MAXN - 1; i >= 0; --i) {
            inv[i] = x * inv[i] % MOD;
            x = x * fact[i] % MOD;
        }
    }

    ll choose(ll n, ll r){
        ll ans = (((fact[n] * inv[r]) % MOD) * inv[n - r]) % MOD;
        return ans;
    }
    factorial(){
        fact.resize(MAXN + 1);
        fact[0] = 1;
        for (int i = 1; i <= MAXN; ++i){
            fact[i] = (fact[i - 1] * i) % MOD;
        }
        invs();
    }

};

/*
 * Number Theory
 */ 

struct euler{ // Sieve of eratosthenes
    const static int MAXN = F;
    vi primes{};
    bool eul[MAXN]{};
    int smallest_factor[MAXN]{};

    void make_primes(){
        iota(smallest_factor, smallest_factor + MAXN, 0);
        eul[0] = true;
        eul[1] = true;
        for (ll i = 2; i < MAXN; ++i){
            if (eul[i] == false){
                primes.push_back(i);
                for (ll j = i * i; j < MAXN; j += i){
                    if (smallest_factor[j] == j){
                        smallest_factor[j] = i;
                    }
                    eul[j] = true;
                }
            }
        }
    }
};

bool isPrime(ll n) { // Miller Rabin algorithm for prime testing
	if (n < 2 || n % 6 % 4 != 1) return (n | 1) == 3;
	ll A[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
    // if ints, use {2, 3, 5, 7}
    // if ll, use {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}
	ll s = __builtin_ctzll(n-1); // count trailing zeroes
    ll d = n >> s;
	for (ll a : A) {
		ll p = modexp(a%n, d, n);
        int i = s;
		while (p != 1 && p != n - 1 && a % n && i--)
        // this is testing (2^(2^r * d) +/- 1) is divis by n
        // from r in 0...s. If so then n is (probably) a prime.
			p = (p * p) % n;
		if (p != n - 1 && i != s) return false;
	}
	return true;
}

struct totient{
    // phi[i] = count of 1 <= i < n s.t. gcd(i, n) = 1
    const int maxn = F;
    vi phi{};
    void pre(){
        phi.assign(maxn, 0);
        iota(phi.begin(), phi.end(), 0);
        // relies on phi[n] = n * prod(1 - 1 / p_i)
        for (int i = 2; i <= maxn; ++i){
            if (phi[i] == i){ // if i is prime
                for (int j = i; j <= maxn; j += i){
                    phi[j] -= phi[j] / i;
                }
            }
        }
    }
};
  
ll chinese_remainder_theorem(vll& a, vll& m, ll A, ll M){
    /*
    * The theorem says if we have m = prod(m0, m1, ... mk)
    * and gcd(mi, mj) = 1 forall i, j, 
    * and a bunch of expressions a === ai mod (mi)
    * then there exists 1 solution to a === ? mod(m)
    * 
    * Here A = prod(a) and M = prod(m)
    */
    ll ans = 0;
    for (int i = 0; i < m.size(); ++i){
        ll M_i = M / m[i]; // the product of everything except m[i]
        ans += ((a[i] * M_i) % M) * modinv(M_i, m[i]);
        ans %= M;
    }
    return ans;        
}

/*
 * Misc.
 */

void bit_ops(unsigned int x){
    // All of these work in cpp20. Part of standard cpp. inputs must be uint
    has_single_bit(x);
    bit_ceil(x); // ceil and floor are to power of 2
    bit_floor(x);
    int s = 2;
    rotl(x, s); // rotates left and right
    rotr(x, s); 
    bit_width(x); 
    countl_zero(x); // counts leading/trailing ones/zeros
    countr_zero(x);
    countl_one(x);
    countr_one(x);
    popcount(x);

    // g++ functions:
    __builtin_popcount(x);
    __builtin_ffs(x); // index of right most set bit, where zero is msb
    __builtin_clz(x); // count leading zeros
    __builtin_ctz(x); // count trailing zeros
    __builtin_parity(x); // parity of the popcount.
}

void matmul(vvi &a, vvi &b, vvi& ab, int n){ // a * b into ab
    ab.assign(n, vi(n, 0));

    for (int i = 0; i < n; ++i){
        for (int j = 0; j < n; ++j){
            for (int k = 0; k < n; ++k){
                ab[i][j] += a[i][k] * b[k][j];
            }
        }
    }
}

void binexp(vvi &a, int k, vvi &res, int n){ // a ^ k into res
    // initialize res to identity matrix
    vvi ans;
    ans.assign(n, vi(n, 0));
    for (int i = 0; i < n; ++i) ans[i][i] = 1;
    vvi ansc = ans;
    while (k){
        if (k & 1){
            ansc = ans;
            matmul(ansc, a, ans, n);
        }
        ansc = ans;
        matmul(ansc, ansc, ans, n);
        k = k >> 1;
    }
    res = ans;
}

/*
 * Data Structures
 */

struct sparsetable{ // For static data
    typedef ll T;
    const static int MAXN = 1e6; // Update
    T f(T a, T b) {return (a + b);} // Update
    T st[25][MAXN];
    int n;
    sparsetable(int n = MAXN):n(n){}

    void insert(int i, T val){ // Do all insert ops first
        st[0][i] = val;
    }
    
    void build(){
        for (int i = 1; i < 25; ++i){
            for (int j = 0; j + (1 << (i - 1)) < n; ++j){
                st[i][j] = f(st[i - 1][j], st[i - 1][j + 1 << (i - 1)]);
            }
        }
    }
    T squery(int L, int R){
        T ans = 0;
        for (int i = 25; i >= 0; --i){
            if ((1 << i) > R - L + 1){
                ans = f(ans, st[i][L]);
                L += (1 << i);
            }
        }
        return ans;
    }
    T mquery(int L, int R){
        int bw; // = bit_width(R - L + 1);
        return f(st[bw][L], st[bw][R - (1 << bw) + 1]);
    }
};

struct mstack{
    typedef ll T;
    T f(T a, T b) {return min(a, b);} // Update
    stack<pair<T, T>> st{};

    void push(T el){
        T newm = st.size() ? el : f(el, st.top().second);
        st.push({el, newm});
    }
    T pop(){
        auto [el, m] = st.top();
        st.pop();
        return el;
    }
    T top(){
        auto [el, m] = st.top();
        return el;
    }
    T mquery(){
        auto [el, m] = st.top();
        return m;
    }
    T size(){
        return st.size();
    }
};

struct mqueue{
    typedef ll T;
    mstack s1{}, s2{};
    void push(T el){
        s1.push(el);
    }
    void transfer(){
        while (s1.size()){
            s2.push(s1.pop());
        }
    }
    T pop(){
        if (s2.size() == 0) transfer();
        auto el = s2.pop();
        return el;
    }
    T size(){
        return s1.size() + s2.size();
    }
};

struct Tree { // segment tree, change unit
    typedef ll T; // The type of the tree elements eg int, ll, etc.
    static constexpr T unit = 0; // the default value of node, for RSQ = 0, for RMinQ +INF, for RMaxQ -INF
    T f(T a, T b) { return (a + b); } // (any associative fn) eg. sum, min, max
    vector<T> s; // tree nodes
    int n; // size of array
    Tree(int n = F, T def = unit) : s(2*n, def), n(n) {} // pass in array size, default value
    void update(int pos, T val) {
        pos += n; // the node corresponding to only pos is at pos + n;
        for (s[pos] = val; pos /= 2;) // pos /= 2 takes us up to our parent node and checks that pos/2 > 0
            // equivalent to (...; pos/2; pos /= 2)
            s[pos] = f(s[pos * 2], s[pos * 2 + 1]); // the parent is function of children
    }
    T query(int b, int e) { // query [b, e) inclusive left, exclusive right
        T ra = unit, rb = unit; // the lower accumulation and upper accumulation are set to default
        b += n; e += n; // start with original b, e locations.
        for (; b < e; b /= 2, e /= 2) { // b/=2 and e/=2 push the bounds up the tree
            if (b % 2) ra = f(ra, s[b++]); // if b is odd, accumulate the answer at b, then make b even
            // we use post-inccrement because we're inclusive at lower bound, check value, then add
            if (e % 2) rb = f(s[--e], rb); // if e is odd, accumulate the answer at e, then make e even
            // we use pre-decrement because we're exclusive at upper bound, subtract first, then check value
        }
        return f(ra, rb); // combine the lower bound accumulation and upper bound accumulation.
    }
};

struct lazy_assignment_segtree{ // this is 1 indexed!
    typedef ll T;
    T f(T a, T b) { return (a + b); }
    struct node {
        int l, r, lazy, val;
    };
    vector<node> t{};
    lazy_assignment_segtree(int n) : t(4 * n + 10) {}
    void build(vll& a, int i, int l, int r) { // a should be 1 indexed as well!
        // vi ilr = {i, l, r};
        // dbg(ilr);
        t[i].l = l;
        t[i].r = r;
        // This might fail if the assignment includes negative values, so handle that
        t[i].lazy = -1; // indicates there is no lazy value to propagate 
        if (l == r) {
            t[i].val = a[l]; return;
        }
        int mid = (l + r) >> 1;
        build(a, i * 2, l, mid);
        build(a, i * 2 + 1, mid + 1, r);
        t[i].val = f(t[i * 2].val, t[i * 2 + 1].val);
    }
    
    void pushdown(int i) {
        if (t[i].lazy == -1) return;

        t[i * 2].lazy = t[i].lazy;
        t[i * 2].val = (t[i * 2].r - t[i * 2].l + 1) * t[i].lazy;
        t[i * 2 + 1].lazy = t[i].lazy;
        t[i * 2 + 1].val = (t[i * 2 + 1].r - t[i * 2 + 1].l + 1) * t[i].lazy;
        t[i].lazy = -1;
    }
    
    void change(int i,int l,int r,int v) {
        if (t[i].l == l && t[i].r == r) {
            t[i].val = v * (r-l+1);
            t[i].lazy = v; 
            return;
        }
        pushdown(i); 
        int mid = (t[i].l + t[i].r) >> 1;
        if (r <= mid) {
            change(i * 2, l, r, v); 
        } else if (l > mid) {
            change(i * 2 + 1, l, r, v); 
        } else {
            change(i * 2, l, mid, v); 
            change(i * 2 + 1, mid + 1, r, v);
        }
        t[i].val = f(t[i * 2].val, t[i * 2 + 1].val);
    }
    
    int query(int i, int l, int r) {
        // cout << i << " " << l << " " << r << endl;
        if (t[i].l == l && t[i].r == r) {return t[i].val;}
        pushdown(i); 
        int mid=(t[i].l + t[i].r) >> 1;
        if (r <= mid) return query(i * 2, l, r);
        if (l > mid) return query(i * 2 + 1, l, r);
        return f(query(i * 2, l, mid), query(i * 2 + 1, mid + 1, r));
    }
};

struct lazy_segment_tree{ // Untested, avoid if possible (You have a fenwick tree that can do this)
    typedef ll T; // The type of the tree elements eg int, ll, etc.
    static constexpr T unit = 0; // the default value of node, for RSQ = 0, for RMinQ +INF, for RMaxQ -INF
    T f(T a, T b) { return (a + b); } // (any associative fn) eg. sum, min, max
    int n; 
    vector<T> st{};
    bool marked[4 * F]{}; // marked for lazy propagation with range assignment
    vector<T> lazy{}; // marked for lazy prop with range update (incr)

    lazy_segment_tree(int n) : st(4 * n, unit), lazy(4 * n), n(n) {}
    void build(vll &a, int v, int tl, int tr){
        if (tl == tr) {st[v] = a[tl]; return;}
        int tm = (tl + tr) / 2;
        build(a, 2 * v, tl, tm);
        build(a, 2 * v + 1, tm + 1, tr); 
        st[v] = f(a[v * 2], a[v * 2 + 1]);
    }
    void push(int v){
        st[2 * v] = st[v];
        st[2 * v + 1] = st[v];
        marked[2 * v + 1] = true;
        marked[2 * v] = true;
        marked[v] = false;
    }
    void push_incr(int v){
        st[2 * v] += lazy[v];
        st[2 * v + 1] += lazy[v];
        lazy[2 * v] += lazy[v];
        lazy[2 * v + 1] += lazy[v];
        lazy[v] = 0;
    }
    void update(int v, int tl, int tr, int l, int r, int incr){
        if (l > r) return;
        if (tl == l && tr == r){
            st[v] += incr;
            lazy[v] += incr;
            return;
        }
        if (lazy[v]) push_incr(v);
        int tm = (tl + tr) / 2;
        update(2 * v, tl, tm, l, min(l, tm), incr);
        update(2 * v + 1, tm + 1, tr, max(tm + 1, l), r, incr);
    }
    void assign(int v, int tl, int tr, int l, int r, int val){
        if (l > r) return;
        if (tl == l && tr == r){
            st[v] = val;
            marked[v] = true;
            return;
        } 
        if (marked[v]) push(v);
        int tm = (tl + tr) / 2;
        assign(2 * v, tl, tm, l, min(l, tm), val);
        assign(2 * v + 1, tm + 1, tr, max(tm + 1, l), r, val);
    }
    int query(int v, int tl, int tr, int l, int r){
        if (l > r) return unit;
        if (tl == l && tr == r) return st[v];
        if (lazy[v]) push_incr(v);
        if (marked[v]) push(v);
        int tm = (tl + tr) / 2;
        return f(query(2 * v, tl, tm, l, min(r, tm)), 
                 query(2 * v + 1, tm + 1, tr, max(l, tm + 1), r));
    }
};

/*
 * Sequences
 */

int subseg_sum(vi &a, int &l, int &r){ // maximum sum subsegment
    int ans = 0; l = 0; r = 1;
    int n = a.size();
    int ms = 0; int cs = 0;
    for (int i = 0; i < n; ++i){
        cs += a[i];
        if (cs - ms > ans){
            r = i + 1;
            ans = cs - ms;
        }
        if (ms > cs){
            l = i;
            ms = cs;
        }
    }
}

struct mex{ // computes the mex of vector a, with updates
    vi a; int n; vi freq;
    set<int> missing{};

    mex(vi const &x) : a(x){
        n = x.size();
        for (int i = 0; i <= n; ++i) missing.insert(i);

        freq.assign(n + 1, 0);
        for (int i : a){
            ++freq[i];
            missing.erase(i);
        }
    }

    int getmex(){
        return *missing.begin();
    }

    void update(int i, int val){
        --freq[a[i]];
        if (freq[a[i]] == 0){
            missing.insert(a[i]);
        }
        a[i] = val;
        ++freq[a[i]];
        if (freq[a[i]] == 1){
            missing.erase(a[i]);
        }
    }
};

struct lis{
    vi a;
    int n;
    vi d{};
    vi dinds{};
    vi par{};
    int ans;

    lis(vi const& a) : a(a){
        n = a.size();
        par.assign(n, -1);

        for (int i = 0; i < n; ++i){
            int ind = lower_bound(d.begin(), d.end(), a[i]) - d.begin();
            if (ind == d.size()){
                d.push_back(ind);
                dinds.push_back(i);
            } else {
                d[ind] = a[i];
                dinds[ind] = i;
            }

            if (ind != 0){
                par[i] = dinds[ind - 1];
            }
        }
        ans = d.size();
    }

    void restore(vi &seq){ // returns the indecies of the LIS, easy fix for vals
        seq.clear();
        int ci = dinds[ans - 1];
        seq.push_back(ci);
        while (par[ci] != -1){
            seq.push_back(par[ci]);
            ci = par[ci];
        }
        reverse(seq.begin(), seq.end());
    }
};

struct DSU{
    // there are many variants of DSU
    int par[F];
    int distto[F]{};
    int rank[F]{};
    DSU(){
        iota(par, par + F, 0);
    }
    int findp(int x){ // no compression
        if (x == par[x]) return x;
        return par[x];
    }
    int findp(int x){ // with tree compression
        if (x == par[x]) return x;
        par[x] = findp(par[x]);
        return par[x];
    }
    void merge(int x, int y){
        int px = findp(x);
        int py = findp(y);
        par[px] = py;
    }
    void merge(int x, int y){ // with union by rank
        int px = findp(x);
        int py = findp(y);
        if (rank[px] < rank[py]) par[px] = py;
        else if (rank[px] > rank[py]) par[py] = px;
        else {par[py] = px; ++rank[px];}
    }
    int findp(int x){ // tracks dist to parent
        // This does path compression and updates dist to parent
        if (x != par[x]){
            int len = distto[par[x]];
            par[x] = findp(par[x]);
            distto[x] += len;
        }
        return par[x];
    }
    void merge(int x, int y){
        int px = findp(x);
        int py = findp(y);
        par[px] = py;
        distto[px] = 1;
    }
    /*
     * Online bipartite check: use the above dist_to_parent version
     * of DSU. If we ever try to merge two nodes that 1) have the same
     * parent and 2) have different parity in dist_to_parent, then we've
     * violated the bipartite conditions.
     */
};

struct fenwick_tree{ // zero indexed fwtree
    vll t;
    ll f(ll a, ll b) { return (a + b); }

    fenwick_tree(int n) : t(n){}
    /*
     * Recall to get right bound is g(l) = l | (l + 1)
     * to get left bound is h(r) = r & (r - 1) + 1
     */
    void update(int pos, int incr){ // point update
        for (; pos < t.size();){
            t[pos] = f(t[pos], incr);
            pos = pos | (pos + 1);
        }
    }

    ll query(int r){ // computes 
        ll ret = 0;
        for (; r >= 0; r = (r & (r + 1)) - 1){
            ret = f(ret, t[r]);
        }
        return ret;
    }

    ll query(int l, int r){
        if (l > 0) return query(r) - query(l - 1);
        return query(r);
    }

    // do not use together with point update!!!
    // delete one of these!!
    void rupdate(int l, int r, ll incr){ // range update 
        update(l, incr);
        update(r + 1, -incr);
    }
    ll pquery(int pos){
        return query(pos);
    }
};

struct fenwick_tree2d{
    vector<vll> fwt;
    int n, m;
    fenwick_tree2d(int n, int m) : n(n), m(m){
        fwt.assign(n, vll(m));
    }
    ll query(int x, int y){ // query first x rows, y cols
        ll ans = 0;
        for (int i = x; i >= 0; i = (i & (i + 1)) - 1){
            for (int j = y; j >= 0; j = (j & (j + 1)) - 1){
                ans += fwt[i][j];
            }
        }
        return ans;
    }
    
    void update(int x, int y, ll incr){
        for (int i = x; i >= 0; i = (i | (i + 1))){
            for (int j = y; j >= 0; j = (j | j + 1)){
                fwt[i][j] += incr;
            }
        }
    }
};

struct fenwick_rurq{
    fenwick_tree b1;
    fenwick_tree b2;
    fenwick_rurq(int n) : b1(n), b2(n) {}

    void update(int l, int r, ll incr){
        b1.update(l, incr);
        b1.update(r + 1, -incr);
        b2.update(l, incr*(l - 1));
        b2.update(r + 1, -incr* r);
    }

    ll query(int r){
        return b1.query(r) * r - b2.query(r);
    }
};

/*
 * Graphs
 */

struct bridge_finding{
    vvi AL{};
    int tin[F]{};
    int low[F]{};
    int tim = 1;
    void dfs(int u, int p){
        tin[u] = tim;
        low[u] = tim;
        int nch = 0;
        ++tim;
        for (int v: AL[u]){
            if (v == p) continue;
            if (tin[v]) {
                low[u] = min(low[u], tin[v]);
                continue;
            }
            dfs(v, u);
            low[u] = min(low[u], low[v]);
            if (low[v] > tin[u]) { // change to >= for art. pt.
                printf("found a brige\n");
            }
            ++nch;
        }
        if (p == -1 && nch > 1) {
            printf("Root is articulation point\n");
        }
    }
};

struct dijk{ // A little speedup with custom cmp fn in set
    vector<vpi> AL{}; // gotta initialize these
    vi d{};
    vi p{};

    void dijks(int s){
        d[s] = 0;
        auto cmp = [&](int i, int j){return d[i] < d[j];}; // <-- if d is global remove &. Also make d global
        set<int, decltype(cmp)> q{}; q.insert(s);
        while (q.size()){
            int u = *q.begin();
            q.erase(u);
            for (auto [v, w] : AL[u]){
                if (d[u] + w < d[v]){
                    q.erase(v); // still gotta do this
                    d[v] = d[u] + w;
                    p[v] = u;
                    q.insert(v);
                }
            }
        }
    }

    void getpath(int t, int s){ // gets path s --> t
        // where we ran dijks(s) at some point.
        vi path{};
        int cur = t;
        while (cur != s){
            path.push_back(cur);
            cur = p[cur];
        }
        path.push_back(s);
        reverse(path.begin(), path.end());
    }
};

struct bellman_ford{ // neg cycles possible, O(VE)
    struct edge{
        int u, v, w;
    };
    vector<edge> EL{}; // initialize these
    vi d{}; // init to all infinity
    vi p{};
    bool has_neg_cyc = false;
    int n;

    void bf(int s){
        d[s] = 0;
        for (int i = 0; i < n - 1; ++i){
            for (auto e : EL){
                if (d[e.u] < INF && d[e.v] > d[e.u] + e.w){
                    d[e.v] = d[e.u] + e.w;
                    p[e.v] = e.u;
                }
            }
        }

        for (auto e : EL){
            if (d[e.v] > d[e.u] + e.w){
                has_neg_cyc = true;
            }
        }
    }
    // get path in dijk struct
};

struct desopo{ // neg edge, no adversary graph
    vector<vpi> AL{}; // gotta initialize these
    vi d{}; // assign inf
    vi p{};
    int n;

    void des(int s){ // can run in exp time, watch out
        vi m(n, 2); // initially, all unvis
        d[s] = 0;
        di q{}; q.push_back(s);

        while (q.size()){
            int u = q.front(); q.pop_front();
            m[u] = 0; // visited
            for (auto [v, w] : AL[u]){
                if (d[v] > d[u] + w){
                    d[v] = d[u] + w;
                    p[v] = u;
                    if (m[v] == 2){
                        q.push_back(v);
                        m[v] = 1; // in queue
                    } else if (m[v] == 0) {
                        q.push_front(v);
                        m[v] = 1;
                    }
                }
            }
        }
    } 
};

struct floyd_warshall{ // All pairs shortest paths APSP
    int n;
    int d[100][100]; // initialize to be AM
    int p[100][100];

    void fw(){
        memset(p, -1, sizeof(p));
        for (int k = 0; k < n; ++k) {
            for (int i = 0; i < n; ++i) {
                for (int j = 0; j < n; ++j) {
                    if (d[i][k] < INF && d[k][j] < INF){
                        d[i][j] = min(d[i][j], d[i][k] + d[k][j]);
                        p[i][j] = k;
                    }                        
                }
            }
        }
    }

    vi r_ans{};
    void reconstruct(int s, int t){ // might be buggy, but this is the idea
        if (s == t){
            r_ans.push_back(s);
            return;
        }
        if (p[s][t] == -1) {
            r_ans.push_back(s);
            r_ans.push_back(t);
            return;
        }
        reconstruct(s, p[s][t]);
        r_ans.push_back(p[s][t]);
        reconstruct(p[s][t], t);
    }
};

struct min_spanning_tree{
    struct edge{
        int u, v, w, id;
        bool operator<(const struct edge& other) { return w < other.w; }
    };
    vector<edge> EL{};
    int par[F];
    int rank[F]{};
    int mst_cost = 0;
    int wto[F]; // weight to the parent.
    vector<edge> mstr{};

    int find(int x){
        return par[x] == x ? x : find(par[x]);
    };

    bool merge(int x, int y, int w){
        int px = find(x);
        int py = find(y);
        if (px == py) return false;

        if (rank[px] < rank[py]){
            par[px] = py;
            wto[px] = w;
        } else {
            par[py] = px;
            wto[py] = py;
            rank[px] += (rank[py] == rank[px]);
        }
        return true;
    }

    void mst(int n){
        sort(EL.begin(), EL.end());
        iota(par, par + n, 0);
        for (auto e : EL){
            auto [u, v, w, id] = e;
            if (merge(u, v, w)) {
                mst_cost += w;
                mstr.push_back(e);
            }
        }
    }

    // for the second best MST
    vector<vpi> ALmst{};
    int tim = 1;
    vi st{};
    vi en{};
    void dfs(int u){
        st[u] = tim;
        ++tim;
        for (auto [v, w] : ALmst[u]){
            if (st[v]) continue;
            dfs(v);
        }
        en[u] = tim;
        ++tim;
    }
    void second_best_mst(int n){
        ALmst.assign(n, vpi());
        st.assign(n, 0);
        en.assign(n, 0);
        for (int i = 0; i < n; ++i){
            if (i == par[i]) continue;
            ALmst[i].push_back({par[i], wto[i]});
            ALmst[par[i]].push_back({i, wto[i]});
        }
        dfs(find(0));
        // use find cycle below this
    }
};

struct find_cycle{ // works for directed & undirected
    vvi AL{};
    vi par{};
    vi vis{};
    vi cyc{};

    void dfs(int u, int p){
        vis[u] = 1; // exploring
        for (int v: AL[u]){
            if (v == p) continue;
            if (vis[v] == 2) continue; // cross edge
            if (vis[v] == 0){
                par[v] = u; 
                dfs(v, u);
                // optional early stop if ans found
                if (cyc.size()) return;
            } else { // vis[v] = 1, back edge
                cyc.clear(); cyc.push_back(u);
                while (cyc.back() != v){
                    cyc.push_back(par[cyc.back()]);
                }
                return;
            }
        }
    }
};

struct LCA{
    vvi AL{};
    vi depth{}; // the depth of each node
    vi first{}; // the first time a node is reached
    vi nodes{}; // the order the nodes were visited in

    void dfs(int u, int p){
        first[u] = nodes.size();
        nodes.push_back(u);
        for (int v : AL[u]){
            if (v == p) continue;
            depth[v] = depth[u] + 1;
            dfs(v, u);
        }
    }

    int lca(int u, int v){
        if (first[u] > first[v]) swap(u, v);
        Tree st{};
        // Modify st to be rmq, fn is 
        // min(depth[u], depth[v])
        st.query(first[u], first[v]);
    }
};

struct LCAb{ // binary lifting

};
struct Dinic {
	struct edge {
		int u, v;
		ll cap; ll fl = 0;
        edge(int u, int v, ll cap) : u(u), v(v), cap(cap) {}
		ll flow() { return max(cap - fl, 0LL); } // if you need flows
	};
	vi lvl; // lvl is level in bfs tree
    vi ptr;  // ptr is indexes into AL
    qi q{}; // queue for bfs
	vvi AL;
    int s, t;
    vector<edge> EL{};
	Dinic(int n, int s, int t) : lvl(n), ptr(n), AL(n), s(s), t(t) {}
	
    void addedge(int u, int v, ll cap, ll rcap = 0) {
        AL[u].push_back(EL.size());
        EL.push_back({u, v, cap});
        AL[v].push_back(EL.size());
        EL.push_back({v, u, rcap});
	}

    bool bfs() {
        while (!q.empty()) {
            int u = q.front();
            q.pop();
            for (int id : AL[u]) {
                if (EL[id].cap - EL[id].fl < 1)
                    continue;
                if (lvl[EL[id].v] != -1)
                    continue;
                lvl[EL[id].v] = lvl[u] + 1;
                q.push(EL[id].v);
            }
        }
        return lvl[t] != -1;
    }

    ll dfs(int u, ll curfl) {
        if (u == t || !curfl) return curfl;
        for (int& i = ptr[u]; i < AL[u].size(); i++) {
            edge& e = EL[AL[u][i]];
            if (lvl[e.v] == lvl[u] + 1){
                ll p = dfs(e.v, min(curfl, e.cap - e.fl));
                if (p) {
                    e.fl += p;
                    EL[AL[u][i] ^ 1].fl -= p;
                    return p;
                }
            }
        }
        return 0;
    }
	ll calc() {
		ll tflow = 0;
		while (true) {
            fill(lvl.begin(), lvl.end(), -1);
            lvl[s] = 0;
            q.push(s);
            if (!bfs())
                break;
            fill(ptr.begin(), ptr.end(), 0);
            while (ll pushed = dfs(s, INF)) {
                tflow += pushed;
            }
        }
        return tflow;
	}
    // once we calculate flow, anything reachable from s
    // is 1 part of set A of the min cut. everything else is set B
	bool leftOfMinCut(int a) { return lvl[a] != -1; }
};

struct MCMF{ // min cost max flow
    struct flowedge{
        int u, v, cap, cost;
        flowedge(int _u, int _v, int _cap, int _cost){
            u = _u; v = _v; cap = _cap; cost = _cost;
        }
    };
    map<pii, int> cost{};
    map<pii, int> cap{};
    // const int ssz = 2004;
    // ll cost[ssz][ssz]{}; // This runs in O(F*n^3) or maybe a little better
    // ll cap[ssz][ssz]{};  // Set these to n limit. If runtime error use map
    vvi AL{};
    vector<flowedge> edges{};
    void spfa(int n, int u0, vi &d, vi &p){ // find shortest path. Populate d with distances and p with parents. Runs in O(mn), but average case better
        d.assign(n, MOD);
        d[u0] = 0;
        bool inq[n]; memset(inq, false, sizeof(inq));
        qi q{};
        q.push(u0); inq[u0] = true;
        p.assign(n, -1);
        while (q.size()){
            int u = q.front(); q.pop();
            inq[u] = false;
            for (int v: AL[u]){
                if (cap[{u , v}] > 0 && d[v] > d[u] + cost[{u , v}]){
                    d[v] = cost[{u , v}] + d[u];
                    p[v] = u;
                    if (!inq[v]){
                        inq[v] = true;
                        q.push(v);
                    }
                }
            }
        }
    }
    pii min_cost_flow(int n, vector<flowedge>& edges, int K, int s, int t){ // K is the flow we need. Can set K to INF for Min cost max flow
        AL.assign(n, vi());
        for (flowedge e: edges){
            AL[e.u].push_back(e.v);
            AL[e.v].push_back(e.u);
            cost[{e.u , e.v}] = e.cost;
            cost[{e.v , e.u}] = -e.cost;
            cap[{e.u , e.v}] = e.cap;
        }
        int fl = 0; int cost = 0;
        vi d, p;
        while (fl < K){ // Can set K to INF still, no worries
            spfa(n, s, d, p);
            if (d[t] == MOD) break;

            int f = K - fl; int cur = t;
            while (cur != s){ // we have a path, find the min capacity on that path
                f = min(f, cap[{p[cur], cur}]);
                cur = p[cur];
            }

            fl += f; cost += f * d[t]; // d is dist but actually cost
            cur = t;
            while (cur != s){ // now we apply the flow
                cap[{p[cur] , cur}] -= f;
                cap[{cur , p[cur]}] += f;
                cur = p[cur];
            }
        }
        return {fl, cost}; // can also return other stuff
    }
};

struct HopcroftKarp{
    /**
     * Fast bipartite matching algorithm. Graph $g$ should be a list
     * of neighbors of the left partition, (i.e. AL.assign(size left partition)) and $btoa$ should be a vector full of
     * -1's of the same size as the right partition. Returns the size of
     * the matching. $btoa[i]$ will be the match for vertex $i$ on the right side,
     * or $-1$ if it's not matched.
     * Usage: vi btoa(m, -1); hopcroftKarp(g, btoa);
     * Time: O(\sqrt{V}E)
     */

    bool dfs(int a, int L, vvi& AL, vi& btoa, vi& A, vi& B) {
        if (A[a] != L) return 0;
        A[a] = -1;
        for (int b : AL[a]) if (B[b] == L + 1) {
            B[b] = 0;
            if (btoa[b] == -1 || dfs(btoa[b], L + 1, AL, btoa, A, B))
                return btoa[b] = a, 1;
        }
        return 0;
    }

    int hopcroftKarp(vvi& AL, vi& btoa) {
        int res = 0;
        vi A(AL.size()), B(btoa.size()), cur, next;
        for (;;) {
            fill(A.begin(), A.end(), 0);
            fill(B.begin(), B.end(), 0);
            /// Find the starting nodes for BFS (i.e. layer 0).
            cur.clear();
            for (int a : btoa) if(a != -1) A[a] = -1;
            for (int a = 0; a < AL.size(); ++a) if(A[a] == 0) cur.push_back(a);
            /// Find all layers using bfs.
            for (int lay = 1;; lay++) {
                bool islast = 0;
                next.clear();
                for (int a : cur) for (int b : AL[a]) {
                    if (btoa[b] == -1) {
                        B[b] = lay;
                        islast = 1;
                    }
                    else if (btoa[b] != a && !B[b]) {
                        B[b] = lay;
                        next.push_back(btoa[b]);
                    }
                }
                if (islast) break;
                if (next.empty()) return res;
                for (int a : next) A[a] = lay;
                cur.swap(next);
            }
            /// Use DFS to scan for augmenting paths.
            for (int a = 0; a < AL.size(); ++a)
                res += dfs(a, 0, AL, btoa, A, B);
        }
    }
};

/*
 * Geometry
 */

ll cross(pll p, pll a, pll b) {
    a.first -= p.first; a.second -= p.second;
    b.first -= p.first; b.second -= p.second;
    return a.first * b.second - a.second * b.first;
}

vi cvxHull(const vpll& v) {
    int ind = min_element(v.begin(), v.end()) - v.begin();
    vi cand{};
    vi hullinds{ind};
    for (int i = 0; i < v.size(); ++i) if (v[i] != v[ind]) cand.push_back(i);

    sort(cand.begin(), cand.end(),[&](int a, int b) { 
        // sort by angle, tiebreak by distance
        pll x = {v[a].first - v[ind].first, v[a].second - v[ind].second};
        pll y = {v[b].first - v[ind].first, v[b].second - v[ind].second}; 
        ll t = cross({0, 0}, x, y);
        return t != 0 ? t > 0 : x.first * x.first + x.second * x.second < y.first * y.first + y.second * y.second; 
    }); 

    // cand is a list of indices (excluding the bottom most, leftmost point) sorted by angle to ind.
    for (int c : cand) {
        // second to last point on stack, last point, current point.
        while (hullinds.size() > 1 && cross(v[hullinds[hullinds.size() - 2]], v[hullinds.back()], v[c]) <= 0) 
            hullinds.pop_back();
        hullinds.push_back(c); 
    }
    return hullinds;
}

/*
 * Strings
 */

struct suffix_array{
    const char* T;
    int n;
    vi RA;
    vi SA;
    vi LCP;
    int alpha_size = 256; // Might be smaller
    void countingSort(int k){ // This is to be used on the rank array RA
        vi c(max(n, alpha_size), 0);
        for (int i = 0; i < n; ++i){
            ++c[i + k < n ? RA[i + k] : 0]; // count frequency of each item
        }
        for (int i = 1; i < alpha_size; ++i){ // Now make cumulative freq.
            c[i] += c[i - 1];
        }
        vi tempSA(n);
        for (int i = 0; i < n; ++i){ // sorts tempSA. For each 
            tempSA[c[SA[i] + k < n ? RA[SA[i] + k] : 0]++] = SA[i];
        }
        swap(SA, tempSA);
    }

    void construct(){
        SA.resize(n);
        iota(SA.begin(), SA.end(), 0);
        RA.resize(n);
        for (int i = 0; i < n; ++i) RA[i] = T[i]; // initial ranking is the character
        for (int k = 1; k < n; k <<= 1){
            countingSort(k);
            countingSort(0);
            vi tempRA(n); // Now we update the rankings of SA, after sorting SA by radix sort
            int r = 0;
            tempRA[SA[0]] = r;
            for (int i = 1; i < n; ++i){
                if ((RA[SA[i]] == RA[SA[i-1]]) && (RA[SA[i]+k] == RA[SA[i-1]+k])) tempRA[SA[i]] = r; 
                else tempRA[SA[i]] = ++r; // compare adj suffixes, same pair => same rank r; otherwise, increase r
            }
            swap(RA, tempRA);
            if (RA[SA[n-1]] == n - 1) break; // This means no ties, so we are done
        }
    }
    suffix_array(char *Tstring, int _n){
        n = _n;
        T = Tstring;
        construct();
    }
    void LCPr(){ // Returns an array that is the longest common prefix of adjacent elements
        vi phi(n); // I'm not sure permuting and repermuting is necessary, but whatever
        vi plcp(n);
        phi[SA[0]] = -1;
        for (int i = 0; i < n; ++i){
            phi[SA[i]] = SA[i - 1];
        }
        int L = 0;
        for (int i = 0; i < n; ++i){
            if (phi[i]== -1){plcp[i] = 0; continue;}
            while (i + L < n && phi[i] + L < n && T[i + L] == T[phi[i] + L]){ // prefix of consecutive elements
                ++L;
            }
            plcp[i] = L;
            if (L > 0) --L;
        }
        LCP.resize(n);
        for (int i = 0; i < n; ++i) LCP[i] = plcp[SA[i]];
        // for LCP of arbitrary inds i, j, do RMQ(LCP, i, j);
    }
    void print_sfx(){
        for (int i = 0; i < n; ++i){
            for (int j = SA[i]; j < n; ++j){
                printf("%c", T[j]);
            }
            printf("\n");
        }
    }
};

struct rolling_hash{ 
    int n;
    vll pows{1}; // make global!
    ll hash[F];
    ll p;
    rolling_hash(string &s, int n, ll p = 31) : n(n), p(p) {
        while (pows.size() <= n){
            pows.push_back((pows.back() * p) % MOD);
        }
        n = s.length();
        hash[0] = 0;
        for (int i = 0; i < n; ++i){
            hash[i + 1] = hash[i] + (pows[i] * (s[i] - 'a' + 1)) % MOD;
            if (hash[i + 1] > MOD) hash[i + 1] -= MOD;
        }

    }
    // Returns the hash value of a substring, [l, r), multiplied by some number pow[n - l] to check equality.
    ll stval(int l, int r){
        ll dif = (hash[r] - hash[l]);
        if (dif < 0) dif += MOD;
        return (dif * pows[n - l]) % MOD;
    }
};

struct pfx_fn{ // KMP algo
    vi pi(const string& s) {
        // Description: pi[x] computes the length of the longest prefix of s that ends at x,
        // other than s[0...x] itself (abacaba -> 0010123).
        vi p(s.length());
        for (int i = 1; i < s.length(); ++i) {
            int g = p[i-1];
            while (g && s[i] != s[g]) g = p[g-1];
            p[i] = g + (s[i] == s[g]);
        }
        return p;
    }

    vi match(const string& s, const string& pat) {
        // finds the indicies of matches between pat(tern) and s
        vi p = pi(pat + "$" + s), res;
        for(int i = pat.length() + 1; i < p.size(); ++i){
            if (p[i] == pat.length()) res.push_back(i - 2 * pat.length());
        }
        return res;
    }

    vi cnt_occ(const string& s){
        // count the occurences of each prefix
        int n = s.length();
        vi p = pi(s);
        vector<int> ans(n + 1);
        for (int i = 0; i < n; i++)
            ans[p[i]]++;
        for (int i = n-1; i > 0; i--)
            ans[p[i-1]] += ans[i];
        for (int i = 0; i <= n; i++)
            ans[i]++;
    }

    int compress(const string& s){
        // is it possible to write s = c * t for some c > 1 ?
        // returns k if possible (such that t = s[:k]), otherwise -1
        vi p = pi(s);
        int k = p.back();
        if (s.length() % k == 0){
            for (int i = 0; i < s.length(); ++i){
                if (s[i] != s[i % k]) return -1;
            }
            return k;
        }
        return -1;
    }
};

struct z_fn{
    // Description: z[x] computes the length of the longest common prefix of s[i:] and s,
    // except z[0] = 0. (abacaba -> 0010301)
    // uses are mostly same as pfx fn

    vi Z(const string& s) {
        vi ans(s.length());
        int n = s.length();
        int l = -1, r = -1;
        for (int i = 1; i < n; ++i) {
            ans[i] = (i >= r) ? 0 : min(r - i, ans[i - l]);
            while (i + ans[i] < n && s[i + ans[i]] == s[ans[i]])
                ans[i]++;
            if (i + ans[i] > r)
                l = i, r = i + ans[i];
        }
        return ans;
    }

};

struct manacher{ // Find d, where d[i] is the number of palindromes centered at i, in O(n) time
    
    vi findp(string &s){ // This only finds odd length palindromes, so preprocess first
        int n = s.length();
        vi d(n + 2, 0);
        s = "$" + s + "@";
        int l = 1;
        int r = 1;
        for (int i = 1; i <= n; ++i){
            d[i] = max(0, min(r - i, d[l + r - i]));
            while (s[d[i] + i] == s[i - d[i]]) ++d[i];
            if (i + d[i] > r) l = i - d[i]; r = i + d[i];
        }
        vi ans(d.begin() + 1, d.end() - 1);
        return ans; // pass reference if this is slow
    }

    string preprocess(string &s){ // since it only finds odd length palindromes
        string t = "x";
        t[0] = s[0];
        for (int i = 1; i < s.size(); ++i){
            string tmp = "#x";
            tmp[1] = s[i];
            t += tmp;
        }
        return t;
    }
};

/*
 * DP
 */

struct sosdp{
    void calc(){
        int n = 20;
        vector<int> a(1 << n);
        // keeps track of the sum over subsets
        // with a certain amount of matching bits in the prefix
        vector<vector<int>> dp(1 << n, vector<int>(n));

        vector<int> sos(1 << n);
        for (int x = 0; x < (1 << 20); ++x){
            dp[x][0] = a[x];
            for (int i = 1; i <= 20; ++i){
                dp[x][i] = dp[x][i - 1];
                if (x & (1 << (i - 1))) dp[x][i] += dp[x ^ (1 << (i - 1))][i - 1];
            }
        }
    }
    void sum_over_supersets(){
        int n = 20;
        vector<int> a(1 << n);
        // keeps track of the sum over subsets
        // with a certain amount of matching bits in the prefix
        vector<vector<int>> dp(1 << n, vector<int>(n));

        vector<int> sos(1 << n);
        for (int i = 0; i < (1<<n); ++i){
            dp[i][0] = a[i];
        }
        for (int x = (1 << 20) -1; x >= 0 ; --x){
            dp[x][0] = a[x];
            for (int i = 1; i <= 20; ++i){
                dp[x][i] = dp[x][i - 1];
                if (x & (1 << (i - 1)) == 0) dp[x][i] += dp[x ^ (1 << (i - 1))][i - 1];
            }
        }
    }
};


int main(){
}

// g++ -o notebook notebook.cpp -fsanitize=undefined -std=c++20
