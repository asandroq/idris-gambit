module Main

-- LFExp	 
-- LFLog	 
-- LFSin	 
-- LFCos	 
-- LFTan	 
-- LFASin	 
-- LFACos	 
-- LFATan	 
-- LFATan2

input : List (String, String)
input = [
  ("exp", "1"),
  ("log", "1"),
  ("sin", "1"),
  ("cos", "1"),
  ("tan", "1")
]

main : IO ()
main = traverse_ (printLn . evalInput) input
where
  evalInput : (String, String) -> Double
  evalInput ("exp", x) = exp (cast x)
  evalInput ("log", x) = log (cast x)
  evalInput ("sin", x) = sin (cast x)
  evalInput ("cos", x) = cos (cast x)
  evalInput ("tan", x) = tan (cast x)
