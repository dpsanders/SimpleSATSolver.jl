module SimpleSATSolver

export SimpleSAT, iterative_solve

import SatisfiabilityInterface: AbstractSATSolver, SATProblem, solve



struct SimpleSAT <: AbstractSATSolver 
end 


include("structured_sat_problem.jl")
include("solve.jl")


# SimpleSAT() = SimpleSAT(false)

# TODO: When a new variable is assigned, check that no clauses are violated

# TODO: Unit propagation


end