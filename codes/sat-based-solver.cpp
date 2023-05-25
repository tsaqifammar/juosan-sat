#include <minisat/core/Solver.h>
#include <bits/stdc++.h>
#include <chrono>
using namespace std;
using Minisat::mkLit;
using Minisat::Lit;

Minisat::Solver solver;

// === Utils ===
void merge(vector<vector<Lit>> &a, vector<vector<Lit>> &b) {
  a.insert(a.end(), b.begin(), b.end());
}
void distribute(Lit t, vector<vector<Lit>>& formula) {
  for (auto& c : formula)
    c.push_back(t);
}
void addFormula(vector<vector<Lit>>& formula) {
  for (auto& c : formula) {
    Minisat::vec<Lit> clause;
    for (auto lit : c) clause.push(lit);
    solver.addClause(clause);
  }
}
// =============

map<array<int,3>, Lit> memo;
int curId = 0;

vector<vector<Lit>> atLeast(int k, vector<Lit>& lits) {
  auto w = [&](int i, int p) -> Lit {
    // A bijective function to map w(i,p) to a unique integer.
    if (memo.find({curId,i,p}) != memo.end()) return memo[{curId,i,p}];
    return memo[{curId,i,p}] = mkLit(solver.newVar());
  };

  auto genForm = [&](Lit a, Lit b, Lit c, Lit d) -> vector<vector<Lit>> {
    // Returns the CNF clauses of "a <-> (b V (c ^ d))"
    return {{~a, b, c}, {~a, b, d}, {a, ~b}, {a, ~c, ~d}};
  };

  vector<vector<Lit>> formula, tmp;
  formula.push_back({w(lits.size(),k)});
  for (int i = 0; i <= lits.size(); i++)
    formula.push_back({w(i,0)});
  for (int p = 1; p <= k; p++)
    formula.push_back({~w(0,p)});
  for (int i = 1; i <= lits.size(); i++)
    for (int p = 1; p <= k; p++)
      tmp = genForm(w(i,p), w(i-1,p), w(i-1,p-1), lits[i-1]), merge(formula, tmp);
  curId++;
  return formula;
}

vector<vector<Lit>> atMost(int k, vector<Lit>& lits) {
  int len = lits.size();
  vector<Lit> neg = lits;
  for (auto& elm : neg) elm = ~elm;
  return atLeast(len - k, neg);
}

vector<vector<Lit>> equals(int k, vector<Lit>& lits) {
  auto f = atLeast(k, lits), f2 = atMost(k, lits);
  merge(f, f2);
  return f;
}

int main() {
  int m, n, r;
  cin >> m >> n >> r;

  vector<vector<Lit>> V(m, vector<Lit>(n));
  for (int i = 0; i < m; i++)
    for (int j = 0; j < n; j++)
      V[i][j] = mkLit(solver.newVar());

  vector<int> N(r);
  for (int i = 0; i < r; i++)
    cin >> N[i];

  vector<vector<Lit>> regionLits(r);
  for (int i = 0, R; i < m; i++)
    for (int j = 0; j < n; j++) {
      cin >> R, R--; // R[i][j]
      regionLits[R].push_back(V[i][j]);
    }
  
  auto start = chrono::steady_clock::now();
  // Add rule: No three vertically consecutive - symbols
  for (int i = 0; i < m - 2; i++)
    for (int j = 0; j < n; j++)
      solver.addClause(~V[i][j], ~V[i+1][j], ~V[i+2][j]);

  // Add rule: No three horizontally consecutive | symbols
  for (int i = 0; i < m; i++)
    for (int j = 0; j < n - 2; j++)
      solver.addClause(V[i][j], V[i][j+1], V[i][j+2]);

  // Add rule: If a territory contains a number, then either
  //           the - or | count is equal to that number.
  vector<Lit> h(r);
  for (int i = 0; i < r; i++) {
    h[i] = mkLit(solver.newVar());
    if (N[i] != -1) {
      auto dashEqual = equals(N[i], regionLits[i]);
      auto barEqual = equals((int) regionLits[i].size()-N[i], regionLits[i]);
      distribute(h[i], dashEqual), distribute(~h[i], barEqual);
      addFormula(dashEqual), addFormula(barEqual);
    }
  }

  bool sat = solver.solve();
  auto finish = chrono::steady_clock::now();
  if (sat) {
    for (int i = 0; i < m; i++)
      for (int j = 0; j < n; j++)
        cout << (solver.modelValue(V[i][j]).isTrue() ? '-' : '|') << " \n"[j == n - 1];
  } else {
    cout << "No solution\n";
  }
  long double timeTaken = chrono::duration_cast<chrono::microseconds>(finish - start).count();
  cout << "Time taken: "<< timeTaken/1000.0 << " ms" << '\n';
}