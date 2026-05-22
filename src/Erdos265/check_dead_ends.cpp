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
};

int main() {
    State init;
    init.num1 = 1; init.den1 = 2;
    init.num2 = 3; init.den2 = 5;
    init.a_prev = 2;
    init.depth = 1;
    
    queue<State> q;
    q.push(init);
    
    int current_depth = 1;
    long long total_nodes = 0;
    long long dead_ends = 0;
    
    cout << "Starting Dead End Analysis for Target S1=1, S2=1.6...\n";
    
    while (!q.empty()) {
        State s = q.front();
        q.pop();
        
        if (s.depth > current_depth) {
            cout << "Depth " << current_depth << ": " << total_nodes << " total paths, " 
                 << dead_ends << " dead ends (" 
                 << (double)dead_ends/total_nodes * 100 << "% die-off)." << endl;
            current_depth = s.depth;
            total_nodes = 0;
            dead_ends = 0;
            
            if (current_depth == 4) break;
        }
        
        total_nodes++;
        
        mpz_class target_a = s.a_prev * s.a_prev;
        mpz_class search_width = 100;
        
        bool has_valid_child = false;
        
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
                has_valid_child = true;
                q.push(next_s);
            }
        }
        
        if (!has_valid_child) {
            dead_ends++;
        }
    }
    
    return 0;
}
