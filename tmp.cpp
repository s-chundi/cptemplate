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

const int MOD = 1e9 + 7;
const int F = 1e5;
const ll INF = 1e18;
int dr[] = {0, 1, -1, 0}; //, 1, -1, 1, -1};
int dc[] = {1, 0, 0, -1}; //, 1, -1, -1, 1};

void solve(){
    ull xc, m; cin >> xc >> m; 
    if (__builtin_popcountll(xc) == 1){
        cout << "-1\n"; return;
    }
    if ((xc ^ m) < xc) {
        cout << "1\n";
        cout << xc << " " << m << '\n';
    } else {
        ll gpttf = 1;
        while (gpttf - 1 <= m){
            gpttf <<= 1;
        }
        gpttf--;
        if ((xc ^ gpttf) < xc && gpttf < xc){
            cout << "2\n";
            cout << xc << " " << gpttf << " " << m << "\n";
        } else cout << "-1\n";
    }
}
/*
    Test ideas on test cases before coding
    Did you read all of the input?
    Did you reset your data structures?
    Are your early exits correct?
    Is overflow possible!?
    Write down all edge cases!
    Don't get stuck on one method!
    Can you create a runtime error to debug?
    All bounds are important!
*/

int main(){
    ios_base::sync_with_stdio(false); cin.tie(0);
    // solve(); return 0;
    int tc; cin >> tc;
    for (int i = 1; i <= tc; ++i){
        solve();
    }
}   
 

// g++ -o tmp tmp.cpp -DLOCAL -fsanitize=undefined -std=c++20