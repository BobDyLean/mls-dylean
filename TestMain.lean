import MLS.Test

def main (args: List String): IO Unit :=
  match args with
  | [] => MLS.Test.main "."
  | [root] => MLS.Test.main root
  | _ => throw (IO.userError "usage: mls-test [directory containing test_vectors/]")
