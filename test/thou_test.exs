defmodule THOUTest do
  use ExUnit.Case
  doctest THOU

  test "greets the world" do
    assert THOU.hello() == :world
  end
end
