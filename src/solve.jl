
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
    print(io, "$(String(action.action)[1]):$(action.literal)")

const actions = Action[]
sizehint!(actions, 1000)

const assignments = Int[]

const unit_literals = Int[]



"""
Process a clause to check sat or find next unassigned variable
`assignments` has -1 if unassigned, 0 or 1 if assigned and false/true respectively

Clause looks like [1, 3, -25]

Returns :sat if the clause is not falsified, :unsat if it is falsified,
:unit if it found a single unassigned literal (i.e. a unit literal)

This assumes that there are no clauses with both x and ¬x in

TODO: Deal with x ∨ ¬x clauses in pre-processing
"""
function process(clause)

    unit_literal = 0

    for literal in clause
        
        variable = index(literal)  
        current = assignments[variable]

        if is_unassigned(current)
            
            if unit_literal != 0   # already found a previous unit literal in the clause
                return :sat, -1  # > 1 literal unassigned in clause, so not falsified 
            end

            unit_literal = literal

              # return :unassigned, literal
         end

        # if any literal in clause has correct value, then clause is satisfiable 
        if current == literal
            return :sat, -1
        end
    end

    # exactly one is unassigned
    if unit_literal != 0
        return :unit, unit_literal 
    end

    # no literals are satisfiable, hence the clause is unsatisfiable
    return :unsat, -1

end



indent(level) = print(" " ^ level)



function check_clauses(p, variable; kw...)
    for clause_number in p.clause_list[variable]
        clause = p.clauses[clause_number]

        status, literal = process(clause)

        # if variable == 12
        #     @show clause, status, literal
        # end

        if status == :unit
            push!(unit_literals, literal)
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
        action = actions[end]
        literal = action.literal

        if literal == original_literal 
            # finished
            return
        end

        variable = index(literal)
        assignments[variable] = unassigned

        pop!(actions)  # remove the action we just processed

    end


end

"""Do unit propagation for the literals implied by `original_literal`.
These were previously collected by `check_clauses`.
"""
function unit_propagation(p, original_literal; kw...)

    if isempty(unit_literals)
        return 
    end

    status = :sat

    if debug(kw)
        @info "Doing unit prop"
        @show assignments
        @show original_literal
    end

    while !isempty(unit_literals)

        literal = popfirst!(unit_literals)
        variable = index(literal)
        push!(actions, Action(:unitprop, literal))

        assignments[variable] = literal

        status, clause = check_clauses(p, variable; kw...)

        if status == :unsat 
            if debug(kw) 
                @info "Unsat: ", clause
            end
            break 
        end

        # no clauses were falsified

    end

    if status == :unsat 
        unassign!(original_literal)  
    end

    empty!(unit_literals)

    return status
end

function assign!(p, literal; kw...)

    variable = index(literal)

    push!(actions, Action(:assign, literal))
    assignments[variable] = literal

    status, clause = check_clauses(p, variable; kw...)

    if status == :unsat 

        if debug(kw)
            @info "Unsat clause: ", clause 
        end
            
        empty!(unit_literals)
        return :unsat
    end

    status = unit_propagation(p, literal; kw...)  # remove this line to remove unit prop

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
    
    empty!(actions)
    empty!(assignments)

    append!(assignments, fill(unassigned, p.num_variables))

   
    backtrack = false

    while true

        if debug(kw)
            # decisions = filter(x -> x.action == :assign, actions)
            # @show decisions

            @show actions

            assigned = filter(is_assigned, assignments)
            @show assigned
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

            if isempty(actions)
                # @error "Action list empty -- should not happen"
                break
            end

            # undo the last action
            action = pop!(actions)

            if action.action == :unitprop   # keep undoing unit props
                variable = index(action.literal)
                assignments[variable] = unassigned
                continue
            end


            literal = action.literal

            variable = index(literal)

            if is_positive(literal)
                # switch positive to negative and try again
                literal = make_literal(variable, -1)

                status = assign!(p, literal; kw...) 

                if status == :sat 
                   backtrack = false  # stop backtracking
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
