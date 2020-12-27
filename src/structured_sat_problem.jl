
"""Boolean satisfiability problem in CNF form.
Like SATProblem but also has 
- `clause_list`: `clause_list[i]` lists clauses containing variable `i`
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

    empty!(action_list)

    status, results = raw_solve(p, fill(unassigned, p.num_variables); kw...)

    if status == :unsat
        return :unsat, Int[]
    end

    return :sat, results
end