defmodule TestCanonical do
  def run do
    test_expr = "(∧::o>o>o a::o b::o)"
    IO.puts("Testing simplify with: #{test_expr}")

    try do
      result = THOU.Canonicalization.Rewriting.simplify(test_expr)
      IO.puts("✓ Success! Result: #{result}")
      :ok
    rescue
      e ->
        IO.puts("✗ Error occurred!")
        IO.inspect(e)
        {:error, e}
    end
  end
end

TestCanonical.run()
