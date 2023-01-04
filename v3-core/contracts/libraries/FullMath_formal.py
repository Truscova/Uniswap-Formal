from z3 import *

           

def negate( number, bits = 256):
    return format(~number & 2 ** bits - 1, "0{}b".format(bits))
    

# mulDiv function from Uniswap-v3 core
def mulDiv_Uniswap ( a,  b,   denominator ):
    
    prod0= BitVec("prod0",256)
    prod00= BitVec("prod00",256)
    prod000= BitVec("prod000",256)
    prod0000= BitVec("prod0000",256)
    
    prod1 = BitVec ("prod1",256)
    mm= BitVec("mm",256)
    result0 = BitVec ("result0",256)
    result1 = BitVec ("result1",256)
    result = BitVec ("result",256)
    remainder = BitVec ("remainder",256)
    denominator1 = BitVec ("denominator1",256)
    
    inv = BitVec ("inv",256)
    inv1 = BitVec ("inv1",256)
    inv2 = BitVec ("inv2",256)
    inv3 = BitVec ("inv3",256)
    inv4 = BitVec ("inv4",256)
    inv5 = BitVec ("inv5",256)
    inv6 = BitVec ("inv6",256)
    
    twos = BitVec ("twos",256)
    twos1 = BitVec ("twos1",256)
    prod11 = BitVec ("prod11",256)
    
    s.add (mm == (a * b) % int(negate(0)))
    s.add (prod0 == a * b)
        
    s.add (If(ULT(mm, prod0), prod1 == mm - prod0 - BitVecVal(0x1, 256), prod1 == mm - prod0 - BitVecVal(0x0, 256)))
    
    
    

    s.add (If (prod1 == 0, And ( UGT (denominator, 0), result0 == prod0/ denominator), result0 == BitVecVal(0x0, 256)))
    
    s.add( If (UGT (remainder, prod0), prod11 == prod1 - BitVecVal(0x1, 256), prod11 == prod1 - BitVecVal(0x0, 256)))
    
    s.add( UGT (denominator, prod1)    )
    s.add (remainder == (a*b) % denominator)
    s.add ( prod00 == prod0 - remainder )
    s.add ( twos == denominator & (~denominator + 1))
    
    
    s.add (denominator1 == denominator / twos)
    s.add (prod000 == prod00 / twos)
    s.add (twos1 == ((0 - twos) / twos) + 1)                
    s.add (prod0000 == prod000 | (prod11 * twos1))
        
                
    s.add (inv == (3 * denominator1)^2)
    s.add (inv1 == inv * (2 - denominator1 * inv))
    s.add (inv2 == inv1 * (2 - denominator1 * inv1))
    s.add (inv3 == inv2 * (2 - denominator1 * inv2))
    s.add (inv4 == inv3 * (2 - denominator1 * inv3))
    s.add (inv5 == inv4 * (2 - denominator1 * inv4))
    s.add (inv6 == inv5 * (2 - denominator1 * inv5))
    
    s.add (result1 == prod0000 * inv6)
                                 
    s.add (If (prod1 == 0, result == result0, result == result1))
    
    return result
    

########################################################################################

'''
https://medium.com/coinmonks/math-in-solidity-part-3-percents-and-proportions-4db014e080b1

function fullMul (uint x, uint y)
public pure returns (uint l, uint h)
{
  uint mm = mulmod (x, y, uint (-1));
  l = x * y;
  h = mm - l;
  if (mm < l) h -= 1;
}

function mulDiv (uint x, uint y, uint z)
public pure returns (uint) {
  (uint l, uint h) = fullMul (x, y);
  require (h < z);  uint mm = mulmod (x, y, z);
  if (mm > l) h -= 1;
  l -= mm;  uint pow2 = z & -z;
  z /= pow2;
  l /= pow2;
  l += h * ((-pow2) / pow2 + 1); 
  
  uint r = 1;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r;
  r *= 2 - z * r; 
  
  return l * r;
}

'''

def mulDiv_medium (x, y, z):

    mm0 = BitVec ("mm0", 256)
    mm1 = BitVec ("mm1", 256)
    l0 = BitVec ("l0", 256)
    l1 = BitVec ("l1", 256)
    l2 = BitVec ("l2", 256)
    l3 = BitVec ("l3", 256)
    
    h0 = BitVec ("h0", 256)
    h1 = BitVec ("h1", 256)
    h2 = BitVec ("h2", 256)
    
    z1 = BitVec ("z1", 256)
    pow2 = BitVec ("pow2", 256)
    
    r0 = BitVec ("r0", 256)
    r1 = BitVec ("r1", 256)
    r2 = BitVec ("r2", 256)
    r3 = BitVec ("r3", 256)
    r4 = BitVec ("r4", 256)
    r5 = BitVec ("r5", 256)
    r6 = BitVec ("r6", 256)
    r7 = BitVec ("r7", 256)
    r8 = BitVec ("r8", 256)
    
    result = BitVec ("result", 256)
    
    #(uint l, uint h) = fullMul (x, y);
    #uint mm = mulmod (x, y, uint (-1));
    s.add (mm0 == (x * y) % int(negate(0)))
    
    #l = x * y;
    s.add (l0 == x * y)
    
    #h = mm - l;
    s.add (h0 == mm0 - l0)
    
    #if (mm < l) h -= 1;
    s.add (If( ULT (mm0, l0), h1 == h0 -1, h1 == h0))
    
    #require (h < z);
    s.add (ULT (h1, z))
    
    #uint mm = mulmod (x, y, z);
    s.add (mm1 == (x * y) % z )
    
    #if (mm > l) h -= 1;
    s.add (If (UGT (mm1, l0), h2 == h1 -1, h2 == h1))
  
    #l -= mm; 
    s.add (l1 == l0 - mm1)
    
    #uint pow2 = z & -z;
    s.add (pow2 == z & -z )
  
    #z /= pow2;
    s.add (z1 == UDiv (z, pow2))
  
    #l /= pow2;
    s.add (l2 == l1 / pow2)
    
    
    #l += h * ((-pow2) / pow2 + 1);
    s.add (l3 == l2 + (h2 * ((0-pow2)/pow2 + 1)))
  
    #uint r = 1;
    s.add (r0 == 1)
  
    #r *= 2 - z * r;
    s.add (r1 == r0 * (2 - z1 * r0))
    
    #r *= 2 - z * r;
    s.add (r2 == r1 * (2 - z1 * r1))
  
    #r *= 2 - z * r;
    s.add (r3 == r2 * (2 - z1 * r2))
  
    #r *= 2 - z * r;
    s.add (r4 == r3 * (2 - z1 * r3))
    
    #r *= 2 - z * r;
    s.add (r5 == r4 * (2 - z1 * r4))
    
    #r *= 2 - z * r;
    s.add (r6 == r5 * (2 - z1 * r5))
  
    #r *= 2 - z * r;
    s.add (r7 == r6 * (2 - z1 * r6))
    
    #r *= 2 - z * r;
    s.add (r8 == r7 * (2 - z1 * r7))
  
    s.add (result == l3 * r8)

    return result;

########################################################################################


X = BitVec("X",256)
Y = BitVec ("Y",256)
denom =  BitVec ("denom",256)


s = Solver()


print ("Creating a new scope - s.add(Not(ForAll (X, ForAll (Y, ForAll (denom,  mulDiv_simple (X,Y,denom) == mulDiv_medium(X,Y,denom))))))")

s.add (X >= 0)
s.add (Y >= 0)
s.add (denom > 0)

s.add(Not(ForAll (X, ForAll (Y, ForAll (denom,  mulDiv_Uniswap (X,Y,denom) == mulDiv_medium(X,Y,denom))))))

ans = s.check()

if ans == sat:
    print (ans)
    print (s.model())
elif ans == unsat:
    print ("unsat")
else:
    print ("unknown")

print ("Restoring original state")


####################

