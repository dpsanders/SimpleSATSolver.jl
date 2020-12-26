module SimpleSATSolver

export SimpleSAT

import SatisfiabilityInterface: AbstractSATSolver, SATProblem, solve



struct SimpleSAT <: AbstractSATSolver 
end 

# SimpleSAT() = SimpleSAT(false)

# TODO: When a new variable is assigned, check that no clauses are violated

# TODO: Unit propagation

"""Boolean satisfiability problem in CNF form.
`contains[i]` is a list of the clauses containing variable `i`.
"""
struct StructuredSATProblem
    num_variables::Int
    clauses::Vector{Vector{Int}} 
    clause_list::Vector{Vector{Int}}
end

function StructuredSATProblem(p::SATProblem)
    
    clauses = sort(p.clauses, by=length)
    clause_list = list_clauses(p.num_variables, clauses)

    return StructuredSATProblem(p.num_variables, clauses, clause_list)
end

"Which clauses contain each variable"
function list_clauses(num_variables, clauses::Vector{Vector{Int}})
    clause_list = [Int[] for i in 1:num_variables]

    for (i, clause) in enumerate(clauses)
        for literal in clause 
            push!(clause_list[value(literal)], i)
        end
    end

    return clause_list
end


solve(p::SATProblem, solver::SimpleSAT; kw...) = 
    solve(StructuredSATProblem(p), solver; kw...)

function solve(p::StructuredSATProblem, solver::SimpleSAT; kw...)
    status, results = raw_solve(p, fill(-1, p.num_variables); kw...)

    if status == :unsat
        return :unsat, Int[]
    end

    return :sat, [results[i] > 0 ? i : -i for i in 1:length(results)]
end

# Literals look like 3, i.e. x₃ or -25, i.e. ¬x₂₅
truth_value(literal) = Int(literal > 0)  # positive is true, negative is false
value(literal) = abs(literal)

is_unassigned(assignments, i) = assignments[i] < 0

"""
Process a clause to check sat or find next unassigned variable
`assignments` has -1 if unassigned, 0 or 1 if assigned and false/true respectively

Clause looks like [1, 3, -25]
"""
function process(clause, assignments)
    for literal in clause
        
        variable = value(literal)  # which variable number

        if is_unassigned(assignments, variable)  # not assigned
            return :unassigned, literal
        end

        # if any literals in the clause have a value which is already assigned, 
        # then the clause is satisfiable 
        if assignments[variable] == truth_value(literal)
            return :sat, -1
        end
    end

    # no literals are satisfiable, hence the clause is unsatisfiable
    return :unsat, -1

end

"""Solve a SAT problem by tree search.
- `assignments` specifies if each variable is unassigned (-1) or assigned with value false (0) or true (1)
- `starting_clause` says which clauses can be skipped since they are satisfied by
the current set of assignments 
"""

indent(level) = print(" " ^ level)


function check_clause(p, assignments, clause, level; kw...)

    if kw[:debug]
        indent(level)
        @show clause
    end

    status, literal = process(clause, assignments)

    if status == :unsat
        if kw[:debug]
            indent(level)
            println("Clause $clause unsat")
        end
                
        return :unsat, assignments 
    end 

    return :sat, assignments
end

function check_clauses(p, variable, assignments, level; kw...)
    for clause_number in p.clause_list[variable]
        clause = p.clauses[clause_number]

        status, assignments = check_clause(p, assignments, clause, level; kw...)

        if status == :unsat 
            return :unsat, assignments 
        end

    end

    return :sat, assignments 
end

"""Solve a problem with the given starting assignments
Starting_clause indicates which clauses have already been processed.
"""
function raw_solve(p, assignments, level=1; kw...)
    
    if kw[:debug]
        println()
        indent(level)
        @show count(>=(0), assignments), assignments
    end


    if count(>=(0), assignments) == length(assignments)  # all satisfied
        return (:sat, assignments)
    end 

    
    variable = findfirst(<(0), assignments)  # choose next unassigned variable

    # variable = level

    assignments[variable] = true

    status, assignments = check_clauses(p, variable, assignments, level; kw...)

    if !(status == :unsat)
        status1, assignments1 = raw_solve(p, assignments, level+1; kw...)
        
        if status1 == :sat 
            return status1, assignments1 
        end 
    end


    assignments[variable] = false

    status, assignments = check_clauses(p, variable, assignments, level; kw...)

    if !(status == :unsat)
        status2, assignments2 = raw_solve(p, assignments, level+1; kw...)
        
        if status2 == :sat 
            return status2, assignments2
        end 
    end

    assignments[variable] = -1 

    return :unsat, assignments 
end


end


