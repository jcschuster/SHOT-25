defmodule THOU.Preprocessing.Rewriting do
  use Rustler, otp_app: :thou
  import THOU.Preprocessing.Serialization

  def canonicalize(term) do
    term
    |> to_s_expr()
    |> simplify()
    |> from_s_expr()
  end

  def simplify(_str), do: :erlang.nif_error(:nif_not_loaded)
end
