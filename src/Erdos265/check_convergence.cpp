#include <iostream>
#include <vector>
#include <gmpxx.h>
#include <queue>

using namespace std;

struct State {
    mpz_class num1, den1;
    mpz_class num2, den2;
    mpz_class a_prev;
    int depth;
    double error_bound; // The strict error bound to beat
};

int main() {
    State init;
    init.num1 = 1; init.den1 = 2;
    init.num2 = 3; init.den2 = 5;
    init.a_prev = 2;
    init.depth = 1;
    init.error_bound = 0.5; // Initial error is 1/2
    
    queue<State> q;
    q.push(init);
    
    int current_depth = 1;
    long long total_nodes = 0;
    long long converging_nodes = 0;
    
    cout << "Starting Convergence BFS for Target S1=1, S2=1.6...\n";
    
    while (!q.empty()) {
        State s = q.front();
        q.pop();
        
        if (s.depth > current_depth) {
            cout << "Depth " << current_depth << ": " << total_nodes << " total paths, " 
                 << converging_nodes << " strictly converging paths (" 
                 << (double)converging_nodes/total_nodes * 100 << "%)." << endl;
            current_depth = s.depth;
            total_nodes = 0;
            converging_nodes = 0;
            
            if (current_depth == 4) break;
        }
        
        mpz_class target_a = s.a_prev * s.a_prev;
        mpz_class search_width = 100;
        
        for (mpz_class cand = target_a - search_width; cand <= target_a + search_width; ++cand) {
            if (cand <= s.a_prev) continue;
            
            State next_s;
            next_s.depth = s.depth + 1;
            next_s.a_prev = cand;
            next_s.num1 = s.num1 * cand - s.den1;
            next_s.den1 = s.den1 * cand;
            next_s.num2 = s.num2 * (cand - 1) - s.den2;
            next_s.den2 = s.den2 * (cand - 1);
            
            if (next_s.num1 <= 0 || next_s.num2 <= 0) continue;
            if (next_s.num2 * next_s.den1 <= next_s.num1 * next_s.den2) continue;
            
            mpz_class lhs = next_s.num1 * next_s.num1 * next_s.den2;
            mpz_class rhs = next_s.num2 * next_s.den1 * next_s.den1 - next_s.num1 * next_s.den1 * next_s.den2;
            
            if (lhs > rhs) {
                total_nodes++;
                
                // Calculate actual error = num1 / den1
                mpf_class num_f(next_s.num1);
                mpf_class den_f(next_s.den1);
                mpf_class error = num_f / den_f;
                
                // If error is shrinking, it's strictly converging
                if (error.get_d() < s.error_bound) {
                    converging_nodes++;
                    next_s.error_bound = error.get_d(); // Require strict monotonic convergence
                } else {
                    next_s.error_bound = s.error_bound; // Failed to shrink, carry old bound
                }
                
                q.push(next_s);
            }
        }
    }
    
    return 0;
}
