module SimpleSATSolver

export SimpleSAT

import SatisfiabilityInterface: AbstractSATSolver, SATProblem, solve



struct SimpleSAT <: AbstractSATSolver 
    unit_prop::Bool
end 

SimpleSAT() = SimpleSAT(false)

struct Action
    type::Symbol
    literal::Int 
end

Base.show(io::IO, a::Action) = print(io, "$(a.type) $(a.literal)")


const actions = Action[]
sizehint!(actions, 100)

const unit_prop_literals = Int[]

unit_prop = false


"""Boolean satisfiability problem in CNF form.
`clause_list[i]` lists the clauses containing variable `i`.

Literals are assumed to be numbered in order, starting at 1
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
            push!(clause_list[index(literal)], i)
        end
    end

    return clause_list
end


solve(p::SATProblem, solver::SimpleSAT; kw...) = 
    solve(StructuredSATProblem(p), solver; kw...)

function solve(p::StructuredSATProblem, solver::SimpleSAT; kw...)

    empty!(actions)

    status, results = raw_solve(p, fill(0, p.num_variables); kw...)

    if status == :unsat
        return :unsat, Int[]
    end

    # return :sat, [results[i] > 0 ? i : -i for i in 1:length(results)]
    return :sat, results

end

##### Main:

truth_value(literal) = Int(literal > 0)  # positive is 1=true, negative is 0=false
index(literal) = abs(literal)  # -25 ↦ 25

# 0 is unassigned 

const unassigned = 0

is_assigned(literal) = literal != unassigned
is_unassigned(literal) = !is_assigned(literal)

num_assigned(assignments) = count(is_assigned, assignments)

"""Undo inferred assignments from unit propagation, 
up to (and including) the variable of interest (`variable`)
"""
function unassign!(assignments, variable)

    # println("Unassigning variable $variable")

    while true
        if isempty(actions)
            return   # shouldn't happen?
        end

        action = pop!(actions)
        # @show action

        current = index(action.literal)

        assignments[current] = unassigned

        if current == variable  # reached destination
            break 
        end
    end
end



"""
Process a clause to check sat/unsat and find an unassigned variable

Clause looks like [1, 3, -25]
"""
function process_clause(clause, assignments)
    # assumes that clause is processed only if there can be 
    # no more than 1 unassigned literal

    unassigned_literal = 0   # not a valid literal

    for literal in clause
        
        variable = index(literal)  # which variable number

        if is_unassigned(assignments[variable])  # not assigned

            if unassigned_literal != 0  # already found a previous unassigned one (which should not happen?)
                return :sat, -1  # can't say anything
            end


            unassigned_literal = literal
            continue
        end

        # if any literal in the clause has the correct assigned value, 
        # then the clause is satisfible 
        if assignments[variable] == literal
            return :sat, -1
        end
    end

    if unassigned_literal != 0
        # there is a single unassigned literal
        # and if we have reached this point then all other literals 
        # are not satisfied 
        # For the clause to be true, the unassigned literal thus has to 
        # take the corresponding value
        return :unassigned, unassigned_literal
    end

    return :unsat, -1

end

"""Solve a SAT problem by tree search.
- `assignments` specifies if each variable is unassigned (-1) or assigned with value false (0) or true (1)
- `starting_clause` says which clauses can be skipped since they are satisfied by
the current set of assignments 
"""

indent(level) = print(" " ^ level)
indent(level, s) = (indent(level); println(s))


function assign!(p, assignments, literal, level, type=:assign; kw...)

    variable = index(literal)
    assignments[variable] = literal

    push!(actions, Action(type, literal))

    if kw[:debug]
        indent(level)
        println("Assigning $literal")
        indent(level)
        @show assignments
    end

    status, assignments = check_clauses(p, variable, assignments, level; kw...)
        
    if status == :unsat 
        unassign!(assignments, variable)

        if kw[:debug]
                indent(level)
                println("Deassigned $variable")
        end

        return :unsat, assignments
    end

    # status == :sat

    status, assignments = raw_solve(p, assignments, level+1; kw...)

    if status == :unsat 
        unassign!(assignments, variable)

        if kw[:debug]
                indent(level)
                println("Deassigned $variable")
        end

        return :unsat, assignments
    end

    return status, assignments
end

# function check_clause(p, assignments, clause, level; kw...)

#     if kw[:debug]
#         indent(level)
#         @show clause
#     end

#     status, literal = process(clause, assignments)

#     if status == :unsat
#         if kw[:debug]
#             indent(level)
#             println("Clause $clause unsat")
#         end
                
#         return :unsat, assignments 
#     end 

#     # if kw[:unit_prop]  # has to be at level of a single clause
#     #     if status == :unassigned 

#     #         if kw[:debug]
#     #             indent(level)
#     #             println("Unit propagation found $literal")
#     #         end

#     #         # status, assignments = assign!(p, assignments, literal, level, :unit_prop; kw...)

#     #     end
#     # end

#     return status, assignments
# end

"Check if clauses containing `variable` are satisfied"
function check_clauses(p, variable, assignments, level; kw...)

    # @info "check_clauses with variable $variable"

    # unit_prop_literals = Int[]

    currently_assigned = num_assigned(assignments)

    for clause_number in p.clause_list[variable]
        clause = p.clauses[clause_number]
        
        # println("Processing clause number $clause_number: $clause")

        if length(clause) >= currently_assigned + 2
            # can't prove (un)satisfiable
            continue 
        end

        status, literal = process_clause(clause, assignments)

        if status == :unsat 
            # unassign!(assignments, variable)
            return :unsat, assignments 
        end

        if unit_prop
            if status == :unassigned
                # try unit propagation

                new_variable = index(literal)
                if is_assigned(assignments, new_variable)
                    current_value = assignments[new_variable]  # current value of the literal we found

                    if current_value != truth_value(literal)  # conflict
                        unassign!(assignments, variable)

                        return :unsat, assigments
                    end

                else  # not assigned 
                    push!(unit_prop_literals, literal)
                end
            end
        end

    end

    if unit_prop
        # @show unit_prop_literals
        while !isempty(unit_prop_literals)
            literal = popfirst!(unit_prop_literals)
            new_variable = index(literal)

            assignments[new_variable] = truth_value(literal)
            push!(actions, Action(:unit_prop, literal))

            status, assignments = check_clauses(p, new_variable, assignments, level+1; kw...)

            if status == :unsat
                unassign!(assignments, variable)
                return status, assignments
            end
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
        println("Entering raw_solve")
        indent(level)
        @show num_assigned(assignments), assignments
        indent(level)
        @show actions
    end


    if num_assigned(assignments) == length(assignments)  # all satisfied
        return (:sat, assignments)
    end 

    
    variable = findfirst(is_unassigned, assignments)  # choose next unassigned variable


    status, assignments = assign!(p, assignments, variable, level; kw...)

    if status == :sat 
        return status, assignments
    end


    status, assignments = assign!(p, assignments, -variable, level; kw...)

    return status, assignments


end


end


