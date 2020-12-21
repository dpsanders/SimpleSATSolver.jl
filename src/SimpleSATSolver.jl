module SimpleSATSolver

export SATProblem, solve

# TODO: When a new variable is assigned, check that no clauses are violated

# TODO: Unit propagation

struct SATProblem
    num_variables::Int
    clauses::Vector{Vector{Int}} 
end

max_var(clause) = maximum(abs, clause)

function SATProblem(clauses::Vector{Vector{Int}})
    num_variables = maximum(max_var, clauses)

    return SATProblem(num_variables, sort(clauses, by=x->length(x)))
end


function solve(p::SATProblem; debug=false)
    status, results = raw_solve(p, fill(-1, p.num_variables), debug=debug)

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
Find next unassigned variable in a clause
`assignments` has -1 if unassigned, 0 or 1 if assigned and false/true respectively

Clause looks like [1, 3, -25]
"""
function find_assignment(clause, assignments)
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

"""Solve a problem with the given starting assignments
Starting_clause indicates which clauses have already been processed.
"""
function raw_solve(p, assignments, starting_clause=1, level=1; debug=false)
    
    if debug
        println()
        indent(level)
        @show count(>=(0), assignments), assignments, starting_clause
    end

    # Choose next variable from shortest clause

    for clause in @view p.clauses[starting_clause:end]

        if debug
            indent(level)
            @show clause
        end

        status, literal = find_assignment(clause, assignments)

        if status == :unsat
            if debug 
                indent(level)
                println("Clause $clause unsat")
            end
            return :unsat, assignments
        
        elseif status == :sat 
            starting_clause += 1
            continue
        end
        

        # unassigned so try both possibilities for that variable
        
        variable = value(literal)   # variable number
        truthiness = truth_value(literal)

        if debug 
            indent(level)
            println("Assigning $literal")
        end

        assignments[variable] = truthiness
        status1, assignments1 = raw_solve(p, assignments, starting_clause, level+1, debug=debug)

        if status1 == :sat 
            return status1, assignments1
        end
 
        assignments[variable] = 1 - truthiness
        status2, assignments2 = raw_solve(p, assignments, starting_clause, level+1, debug=debug)

        if status2 == :sat 
            return status2, assignments2 
        end

        if debug
            indent(level)
            println("Clause $clause unsat")
        end

        # If here then neither value of the current variable is satisfiable
        assignments[variable] = -1  # unassign
        return :unsat, assignments
    end

    return :sat, assignments

end


end



