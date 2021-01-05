module SimpleSATSolver

export SimpleSAT, iterative_solve

import SatisfiabilityInterface: AbstractSATSolver, SATProblem, solve



struct SimpleSAT <: AbstractSATSolver 
end 


struct Action 
    action::Symbol 
    literal::Int
end

Base.show(io::IO, action::Action) = 
    print(io, "$(String(action.action)[1]):$(action.literal)")

const actions = Action[]
sizehint!(actions, 1000)

const assignment = Int[]

const unit_literals = Int[]


include("structured_sat_problem.jl")
include("solve.jl")


# SimpleSAT() = SimpleSAT(false)

# TODO: When a new variable is assigned, check that no clauses are violated

# TODO: Unit propagation


end