module SimpleSATSolver

export SATProblem, solve

# TODO: When a new variable is assigned, check that no clauses are violated

# TODO: Unit propagation

struct SATProblem
    num_variables::Int
    clauses::Vector{Vector{Int}} 
end

max_var(clause) = maximum(abs.(clause))

function SATProblem(clauses::Vector{Vector{Int}})
    num_variables = maximum(max_var.(clauses))

    return SATProblem(num_variables, sort(clauses, by=x->length(x)))
end


function solve(p::SATProblem; debug=false)
    status, results = raw_solve(p, BitArray(falses(p.num_variables)), BitArray(falses(p.num_variables)), debug=debug)

    if status == :unsat
        return :unsat, nothing
    end

    return :sat, [results[i] > 0 ? i : -i for i in 1:length(results)]
end


truth_value(literal) = literal > 0  # positive is true, negative is false

"Find next unassigned variable in a clause"
function find_assignment(p, clause, assigned, assignments)
    for literal in clause
        
        variable = abs(literal)

        if !assigned[variable]
            return :unassigned, literal
        end

        # if any are correct, 
        # then the clause is satisfiable with the already-assigned variables
        if assignments[variable] == truth_value(literal)
            return :sat, -1
        end
    end

    # must be unsatisfiable
    return :unsat, -1

end

"""Solve a SAT problem by tree search.
- `assigned` specifies which variables already have `assignments` (true or false)
- `starting_clause` says which clauses can be skipped since they are satisfied by
the current set of assignments 
"""

indent(level) = print(" " ^ level)

function raw_solve(p, assigned, assignments, starting_clause=1, level=1; debug=false)
    assigned = copy(assigned)
    solution = copy(assignments)
    
    if debug
        println()
        indent(level)
        @show count(assigned), assigned, assignments, starting_clause
    end

    # Choose next variable from shortest clause

    for clause in p.clauses[starting_clause:end]

        if debug
            indent(level)
            @show clause
        end

        status, literal = find_assignment(p, clause, assigned, assignments)

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
        
        variable = abs(literal)
        truthiness = truth_value(literal)

        if debug 
            indent(level)
            println("Assigning $literal")
        end

        assigned[variable] = true 
        assignments[variable] = truthiness
        status1, assignments1 = raw_solve(p, assigned, assignments, starting_clause, level+1, debug=debug)

        if status1 == :sat 
            return status1, assignments1
        end
 
        assignments[variable] = !truthiness
        status2, assignments2 = raw_solve(p, assigned, assignments, starting_clause, level+1, debug=debug)

        if status2 == :sat 
            return status2, assignments2 
        end

        if debug
            indent(level)
            println("Clause $clause unsat")
        end
        return :unsat, missing 
    end

    return :sat, assignments

end

end