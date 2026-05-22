import sys
from fractions import Fraction

sys.set_int_max_str_digits(1000000)

# Kovač and Tao used interval halving. 
# We need to find if there is a deterministic parity-switching logic.
# Let's write a BFS that ONLY branches when absolutely necessary to avoid a dead end.
