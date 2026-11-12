# run_all.jl -- runs every verification script and adds up their summary counts.
#
#   julia run_all.jl
#
# Each script prints PASS/FAIL lines and a last line "SUMMARY: p passed, f failed"; the output
# of every script is copied to the screen. The exit code is 0 when nothing failed.

const SCRIPTS = ["verify_systems.jl", "odd_families.jl", "blocks.jl", "regions.jl", "eulerian.jl",
                 "caged.jl", "dumont.jl", "hankel.jl", "canon.jl", "steiner.jl", "searches.jl"]

function main()
    julia = Base.julia_cmd()
    totalp = 0; totalf = 0; rows = String[]; t0 = time()
    for s in SCRIPTS
        println("=" ^ 78); println("### ", s); flush(stdout)
        t = time()
        out = IOBuffer()
        proc = run(pipeline(ignorestatus(`$julia --startup-file=no $(joinpath(@__DIR__, s))`); stdout=out, stderr=out))
        text = String(take!(out)); print(text)
        m = match(r"SUMMARY: (\d+) passed, (\d+) failed", text)
        if m === nothing || (proc.exitcode != 0 && parse(Int, m[2]) == 0)
            println("FAIL: $s did not finish"); totalf += 1
            push!(rows, rpad(s, 22) * "did not finish")
        else
            p = parse(Int, m[1]); f = parse(Int, m[2]); totalp += p; totalf += f
            push!(rows, rpad(s, 22) * lpad(p, 5) * " passed" * lpad(f, 4) * " failed" * lpad(round(time() - t; digits=1), 8) * " s")
        end
    end
    println("=" ^ 78)
    foreach(println, rows)
    println("TOTAL: $totalp passed, $totalf failed  (", round(time() - t0; digits=1), " s)")
    exit(totalf == 0 ? 0 : 1)
end

main()
