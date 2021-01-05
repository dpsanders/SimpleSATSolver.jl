
"""Boolean satisfiability problem in CNF form.
Like SATProblem but also has 
- `clause_list`: `clause_list[i]` lists clauses containing variable `i`
"""

struct StructuredSATProblem
    num_variables::Int
    clauses::Vector{Vector{Int}} 
    clause_list::Vector{Vector{Int}}
end

function StructuredSATProblem(num_variables, clauses)
    clauses2 = sort(clauses, by=length)
    clause_list = list_clauses(num_variables, clauses2)

    return StructuredSATProblem(num_variables, clauses2, clause_list)
end

StructuredSATProblem(p::SATProblem) = StructuredSATProblem(p.num_variables, p.clauses)
    

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



"Preprocess by removing unit clauses and assigning the resulting variables.
Modifies assignment"
function preprocess(p::SATProblem)

    empty!(assignment)
    append!(assignment, fill(unassigned, p.num_variables))

    empty!(unit_literals)

   
    new_clauses = Vector{Int}[]

    for clause in p.clauses
        if length(clause) == 1   # unit clause determines variable value
            literal = clause[1]
            variable = index(literal)

            assignment[variable] = literal

        else
            push!(new_clauses, clause)
        end
    end

    return StructuredSATProblem(p.num_variables, new_clauses)

end


function solve(p::SATProblem, solver::SimpleSAT; kw...) 
    
    pp = preprocess(p)

    status, assignment = iterative_solve(pp; kw...)

    if status == :unsat
        return :unsat, Int[]
    end

    return :sat, assignment
end
    
# function solve(p::StructuredSATProblem, solver::SimpleSAT; kw...)

#     status, results = iterative_solve(p; kw...)

#     if status == :unsat
#         return :unsat, Int[]
#     end

#     return :sat, results
# end

