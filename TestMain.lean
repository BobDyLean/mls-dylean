import Mls.Test

def main (args: List String): IO Unit :=
  match args with
  | [] => Mls.Test.main "."
  | [root] => Mls.Test.main root
  | _ => throw (IO.userError "usage: mls-test [directory containing test_vectors/]")
