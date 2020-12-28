
## Literals

# Literals look like 3, i.e. x₃ or -25, i.e. ¬x₂₅
# truth_index(literal) = Int(literal > 0)  # positive is true, negative is false

# assignments are like [1, -2, 3, -4]

debug(kw) = haskey(kw, :debug) && kw[:debug]


const unassigned = 0

index(literal) = abs(literal)   # which variable a literal is: index(-3) == 3
is_unassigned(literal) = literal == unassigned
is_assigned(literal) = literal != unassigned

is_positive(literal) = literal > 0

make_literal(variable, sign) = copysign(variable, sign)

num_assigned(assignments) = count(is_assigned, assignments)

struct Action 
    action::Symbol 
    literal::Int
end

Base.show(io::IO, action::Action) = 
    println(io, "$(action.action): $(action.literal)")

const action_list = Action[]
sizehint!(action_list, 1000)

const assignments = Int[]

const unit_prop_literals = Int[]



"""
Process a clause to check sat or find next unassigned variable
`assignments` has -1 if unassigned, 0 or 1 if assigned and false/true respectively

Clause looks like [1, 3, -25]
"""
function process(clause)

    unassigned_literal = 0

    for literal in clause
        
        variable = index(literal)  
        current = assignments[variable]

        if is_unassigned(current)
            
            if unassigned_literal != 0
                return :sat, -1  # >= 2 unassigned, so not falsified 
            end

            unassigned_literal = literal

              # return :unassigned, literal
         end

        # if any literal in clause has correct value, then clause is satisfiable 
        if current == literal
            return :sat, -1
        end
    end

    # exactly one is unassigned
    if unassigned_literal != 0
        return :unassigned, unassigned_literal 
    end

    # no literals are satisfiable, hence the clause is unsatisfiable
    return :unsat, -1

end



indent(level) = print(" " ^ level)



function check_clauses(p, variable; kw...)
    for clause_number in p.clause_list[variable]
        clause = p.clauses[clause_number]

        status, literal = process(clause)

        if status == :unassigned
            push!(unit_prop_literals, literal)
        end

        if status == :unsat 
            return :unsat, clause 
        end

    end

    return :sat, Int[]
end

"Unassign actions back to given literal"
function unassign!(original_literal)
    while true 
        action = action_list[end]
        literal = action.literal

        if literal == original_literal 
            # finished
            return
        end

        variable = index(literal)
        assignments[variable] = unassigned

        pop!(action_list)  # remove the action we just processed

    end


end

function unit_prop(p, original_literal; kw...)

    status = :sat

    if debug(kw)
        @info "Unit prop literals: ", unit_prop_literals
    end

    while !isempty(unit_prop_literals)

        literal = popfirst!(unit_prop_literals)
        variable = index(literal)

        assignments[variable] = literal

        status, clause = check_clauses(p, variable; kw...)

        if status == :unsat 
            if debug(kw) 
                @info "Unsat: ", clause
            end
            break 
        end

        # no clauses were falsified
        push!(action_list, Action(:unit_prop, literal))

    end

    if status == :unsat 
        unassign!(original_literal)  
    end

    empty!(unit_prop_literals)

    return status
end

function assign!(p, literal; kw...)

    variable = index(literal)

    push!(action_list, Action(:assign, literal))
    assignments[variable] = literal

    status, clause = check_clauses(p, variable; kw...)

    if status == :unsat 

        if debug(kw)
            @info "Unsat clause: ", clause 
        end
            
        empty!(unit_prop_literals)
        return :unsat
    end

    status = unit_prop(p, literal; kw...)

    return status

end


function select_variable(assignments)

    ## random choice:
    # possible = (1:length(assignments))[is_unassigned.(assignments)]
    # return rand(possible)
    
    ## first available:
    variable = findfirst(is_unassigned, assignments)
end


iterative_solve(p; kw...) = 
    iterative_solve(StructuredSATProblem(p); kw...)

"""Solve a SAT problem by tree search.
- `assignments` specifies if each variable is unassigned (-1) or assigned with index false (0) or true (1)
- `starting_clause` says which clauses can be skipped since they are satisfied by
the current set of assignments 
"""
function iterative_solve(p::StructuredSATProblem; kw...)
    
    empty!(action_list)
    empty!(assignments)

    append!(assignments, fill(unassigned, p.num_variables))

   
    backtrack = false

    while true

        if debug(kw)
            @show action_list 
            @show assignments
        end

        if !backtrack

            if num_assigned(assignments) == p.num_variables
                # finished!
                return :sat, assignments
            end

            # choose and assign a new variable:
            variable = select_variable(assignments)
            literal = make_literal(variable, 1)

            status = assign!(p, literal; kw...) 

            if status == :unsat 
                backtrack = true 
            end
            
        else # backtrack 
            if debug(kw)
                @info "Backtracking..."
            end

            if isempty(action_list)
                @error "Action list empty -- should not happen"
                break
            end

            # undo the last action
            action = pop!(action_list)
            literal = action.literal

            variable = index(literal)

            if is_positive(literal)
                # switch positive to negative and try again
                literal = make_literal(variable, -1)

                status = assign!(p, literal; kw...) 

                if status == :sat 
                    backtrack = false 
                end
            
            else
                # neither assignment to variable worked
                # keep backtracking
                assignments[variable] = unassigned
            end

        end

    end

    return :unsat, assignments

end
