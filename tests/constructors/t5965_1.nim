discard """
  errormsg: "Invalid field assignment '2'"
  file: "t5965_1.nim"
  line: 10
"""

type Foo = object
  a, b, c: int

discard Foo(a: 1, 2)
