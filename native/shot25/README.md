# NIF for SHOT25.Preprocessing.Rewriting

## To build the NIF module:

- Your NIF will now build along with your project.

## To load the NIF:

```elixir
defmodule SHOT25.Preprocessing.Rewriting do
  use Rustler, otp_app: :SHOT25, crate: "shot25"

  # When your NIF is loaded, it will override these functions.
  def egg_simplify(_str), do: :erlang.nif_error(:nif_not_loaded)
  def egg_simplify_ac(_str), do: :erlang.nif_error(:nif_not_loaded)
end
```

## Examples

[This](https://github.com/rusterlium/NifIo) is a complete example of a NIF
written in Rust.
