#!/usr/bin/env elixir

Mix.start()
Mix.Project.in_project(:thou, ".", fn _module ->
  Mix.Task.run("compile")
end)

# Test the canonicalize function
test_expr = "(∧::o>o>o a::o b::o)"
IO.puts("Testing simplify with: #{test_expr}")

try do
  result = THOU.Canonicalization.Rewriting.simplify(test_expr)
  IO.puts("Result: #{result}")
rescue
  e ->
    IO.inspect(e)
    IO.puts("Error occurred!")
end
