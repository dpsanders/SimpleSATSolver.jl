using SimpleSATSolver
using SatisfiabilityInterface
using Test


function is_sat(p::SATProblem)
    status, results = solve(p, SimpleSAT())

    return status == :sat && satisfies(p, results)
end

function is_unsat(p::SATProblem)
    status, results = solve(p, SimpleSAT())

    return status == :unsat
end


is_sat(v::Vector{Vector{Int}}) = is_sat(SATProblem(v))
is_unsat(v::Vector{Vector{Int}}) = is_unsat(SATProblem(v))


@testset "SimpleSATSolver.jl" begin
    @test is_sat([ [2] ])
    @test is_sat([ [1, -5, 4], [-1, 5, 3, 4], [-3, -4] ])
    @test is_sat([[1, 2], [-1, 3], [-3, -2], [-1, 3], [-1, -3]])

    @test is_unsat([ [1], [-1] ])

    @test is_sat([ [1, 2], [-1, 3], [-3, -2], [-1, 3], [-1, -3] ])  # forces backtracking

    # 2-colouring of linear graph with 3 vertices:
    @test is_sat( [[1, 2], [-1, -2], [3, 4], [-3, -4], [5, 6], [-5, -6], [-1, -3], [-2, -4], [-3, -5], [-4, -6]] )

    # 3-colouring of ring with 11 vertices:
    @test is_sat( [[1, 2, 3], [-1, -2], [-1, -3], [-2, -3], [4, 5, 6], [-4, -5], [-4, -6], [-5, -6], [7, 8, 9], [-7, -8], [-7, -9], [-8, -9], [10, 11, 12], [-10, -11], [-10, -12], [-11, -12], [13, 14, 15], [-13, -14], [-13, -15], [-14, -15], [16, 17, 18], [-16, -17], [-16, -18], [-17, -18], [19, 20, 21], [-19, -20], [-19, -21], [-20, -21], [22, 23, 24], [-22, -23], [-22, -24], [-23, -24], [25, 26, 27], [-25, -26], [-25, -27], [-26, -27], [28, 29, 30], [-28, -29], [-28, -30], [-29, -30], [31, 32, 33], [-31, -32], [-31, -33], [-32, -33], [-1, -4], [-2, -5], [-3, -6], [-4, -7], [-5, -8], [-6, -9], [-7, -10], [-8, -11], [-9, -12], [-10, -13], [-11, -14], [-12, -15], [-13, -16], [-14, -17], [-15, -18], [-16, -19], [-17, -20], [-18, -21], [-19, -22], [-20, -23], [-21, -24], [-22, -25], [-23, -26], [-24, -27], [-25, -28], [-26, -29], [-27, -30], [-28, -31], [-29, -32], [-30, -33], [-31, -1], [-32, -2], [-33, -3]])

    @testset "Load file" begin 
        p = read_cnf("factorisation.cnf")
        @test is_sat(p)
    end

end


