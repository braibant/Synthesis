Test the divide and conquer adder that was generated (using a for
loop, to iterate test cases).

Note that we use the following convention in our Coq representation:
given the input sequence 

input	1101100100011100100110011000001100010110100010010100101010000010

that corresponds to 

          0:	 2	(0010)
          1:	 8	(1000)
          2:	10	(1010)
          3:	 4	(0100)
          4:	 9	(1001)
          5:	 8	(1000)
          6:	 6	(0110)
          7:	 1	(0001)
          8:	 3	(0011)
          9:	 8	(1000)
         10:	 9	(1001)
         11:	 9	(1001)
         12:	12	(1100)
         13:	 1	(0001)
         14:	 9	(1001)
         15:	13	(1101)

we produce the following output sequence 

output	0001000100100011010001101000100010001001100110011001101011001101

that corresponds to 

          0:	13	(1101)
          1:	12	(1100)
          2:	10	(1010)
          3:	 9	(1001)
          4:	 9	(1001)
          5:	 9	(1001)
          6:	 9	(1001)
          7:	 8	(1000)
          8:	 8	(1000)
          9:	 8	(1000)
         10:	 6	(0110)
         11:	 4	(0100)
         12:	 3	(0011)
         13:	 2	(0010)
         14:	 1	(0001)
         15:	 1	(0001)

This is expected: our encoding of tuples in Fe-Si  considers the
4'b0001 as the first element of the 16-uple. 
