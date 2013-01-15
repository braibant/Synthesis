Showcase the implementation of the stack machine. 

The machine is loaded with code that computes a given value of the
Fibonacci sequence. The value is stored in the program bitmap. Use the
ocaml program fibonacci.ml to generate other program bitmaps for other
values.

Our semantics predics that the output result for the initial value 10
is as follows 

pc:36	 sp:0
code at pc: 12'b000000001011
stack[0]:       55
stack[1]:       10
stack[2]:        0
stack[3]:        0
stack[4]:        0
stack[5]:        0
stack[6]:        0
stack[7]:        0

store [0]:       55
store [1]:       55
store [2]:       34
store [3]:       55
store [4]:       10
store [5]:        0
store [6]:        0
store [7]:        0

Our simulated executions indeed produces the following result:
pc: 36	sp:  0
code at pc:000000001011
opcode:000000001011
guard: 1, value: 0
stack[          0]:  55
stack[          1]:  10
stack[          2]:   0
stack[          3]:   0
stack[          4]:   0
stack[          5]:   0
stack[          6]:   0
stack[          7]:   0

store [          0]:  55
store [          1]:  55
store [          2]:  34
store [          3]:  55
store [          4]:  10
store [          5]:   0
store [          6]:   0
store [          7]:   0
