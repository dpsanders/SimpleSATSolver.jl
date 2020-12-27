
## Literals

# Literals look like 3, i.e. x₃ or -25, i.e. ¬x₂₅
# truth_index(literal) = Int(literal > 0)  # positive is true, negative is false

# assignments are like [1, -2, 3, -4]

debug(kw) = haskey(kw, :debug) && debug(kw)


const unassigned = 0

index(literal) = abs(literal)   # which variable a literal is: index(-3) == 3
is_unassigned(literal) = literal == unassigned
is_assigned(literal) = literal != unassigned

make_literal(variable, sign) = copysign(variable, sign)

"""
Process a clause to check sat or find next unassigned variable
`assignments` has -1 if unassigned, 0 or 1 if assigned and false/true respectively

Clause looks like [1, 3, -25]
"""
function process(clause, assignments)
    for literal in clause
        
        variable = index(literal)  

        current_value = assignments[variable]

        if is_unassigned(current_value)  
            return :unassigned, literal
        end

        # if any literal in clause has correct value, then clause is satisfiable 
        if current_value == literal
            return :sat, -1
        end
    end

    # no literals are satisfiable, hence the clause is unsatisfiable
    return :unsat, -1

end

"""Solve a SAT problem by tree search.
- `assignments` specifies if each variable is unassigned (-1) or assigned with index false (0) or true (1)
- `starting_clause` says which clauses can be skipped since they are satisfied by
the current set of assignments 
"""

indent(level) = print(" " ^ level)


function check_clause(p, assignments, clause, level; kw...)

    if debug(kw)
        indent(level)
        @show clause
    end

    status, literal = process(clause, assignments)

    if status == :unsat
        if debug(kw)
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
    
    if debug(kw)
        println()
        indent(level)
        @show count(is_assigned, assignments), assignments
    end


    if count(is_assigned, assignments) == length(assignments)  # all satisfied
        return (:sat, assignments)
    end 

    
    variable = findfirst(is_unassigned, assignments)  # choose next unassigned variable

    # variable = level

    literal = make_literal(variable, 1)
    assignments[variable] = literal

    status, assignments = check_clauses(p, variable, assignments, level; kw...)

    if !(status == :unsat)
        status, assignments = raw_solve(p, assignments, level+1; kw...)
        
        if status == :sat 
            return status, assignments
        end 
    end


    literal = make_literal(variable, -1)
    assignments[variable] = literal

    status, assignments = check_clauses(p, variable, assignments, level; kw...)

    if !(status == :unsat)
        status, assignments = raw_solve(p, assignments, level+1; kw...)
        
        if status == :sat 
            return status, assignments
        end 
    end

    
    assignments[variable] = unassigned

    return :unsat, assignments 
end


