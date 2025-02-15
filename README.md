# distribution_factors

This is an attempt to formalize the theorems in https://www.arxiv.org/abs/2412.16164 which derive common DC loadflow elements in a unified manner. If successful, this could serve as the starting point for other DC loadflow math proofs as I will build up the DC loadflow equations from the ground up.

# State

Currently I wrote down a graph for DC grids and defined the usual DC assumptions
(kirchhoff, balanced, loopless, nonzero_b).
From this I was already able to derive
- antisymmetry of flows
- If you sum all edges to a node that's the same as summing all node-to-node flows. So I have two ways of writing kirchhoff now.
- Equation 4 + 5 in the paper (Matrix form equal to kirchhoff)

Next up, equation 6+7! 