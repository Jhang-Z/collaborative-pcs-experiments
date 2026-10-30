"""Independent Keccak-f oracle using the compact lane-cycle algorithm.
No Rust circuit builder, R1CS constants/layout, or sponge/hash interface is used.
"""
MASK=(1<<64)-1
RC=(0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000080008081,0x8000000000008080,0x80000001,0x8000000080008008)
ROT=(1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44)
PI=(10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1)
def rol(x,n):return ((x<<n)|(x>>(64-n)))&MASK

def permutation(data):
    assert len(data)==200
    s=[int.from_bytes(data[i:i+8],'little') for i in range(0,200,8)]
    for rc in RC:
        c=[s[x]^s[x+5]^s[x+10]^s[x+15]^s[x+20] for x in range(5)]
        for x in range(5):
            d=c[(x-1)%5]^rol(c[(x+1)%5],1)
            for y in range(0,25,5):s[y+x]^=d
        last=s[1]
        for rot,target in zip(ROT,PI):last,s[target]=s[target],rol(last,rot)
        for row in range(0,25,5):
            old=s[row:row+5]
            for x in range(5):s[row+x]=(old[x]^((~old[(x+1)%5])&old[(x+2)%5]))&MASK
        s[0]^=rc
    return b''.join(x.to_bytes(8,'little') for x in s)

def outputs(data):
    assert len(data)%200==0
    return b''.join(permutation(data[i:i+200])[:32] for i in range(0,len(data),200))

assert permutation(bytes(200))[:32].hex()=='e7dde140798f25f18a47c033f9ccd584eea95aa61e2698d54d49806f304715bd'
