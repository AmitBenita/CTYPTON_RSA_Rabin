import random
from sympy import isprime

# Type definitions
u1byte = int  # 8-bit unsigned integer
u2byte = int  # 16-bit unsigned integer
u4byte = int  # 32-bit unsigned integer

s1byte = int  # 8-bit signed integer
s2byte = int  # 16-bit signed integer
s4byte = int  # 32-bit signed integer


# Function prototypes
def cipher_name():
    return ["crypton1", "crypton1.py", ""]


# Circular rotate of 32 bit values
def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF


def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & 0xFFFFFFFF


# Invert byte order in a 32 bit variable
def bswap(x):
    return (rotl(x, 8) & 0x00ff00ff) | (rotr(x, 8) & 0xff00ff00)


# Extract byte from a 32 bit quantity (little endian notation)
def byte(x, n):
    return (x >> (8 * n)) & 0xFF


# For inverting byte order in input/output 32 bit words if needed
BLOCK_SWAP = False  # Set this based on your needs
BYTE_SWAP = BLOCK_SWAP
WORD_SWAP = BLOCK_SWAP


def io_swap(x):
    return bswap(x) if BYTE_SWAP else x


# For inverting the byte order of input/output blocks if needed
if WORD_SWAP:
    def get_block(x, in_blk):
        x[0], x[1], x[2], x[3] = (io_swap(in_blk[3]), io_swap(in_blk[2]),
                                  io_swap(in_blk[1]), io_swap(in_blk[0]))

    def put_block(x, out_blk):
        out_blk[3], out_blk[2], out_blk[1], out_blk[0] = (io_swap(x[0]), io_swap(x[1]),
                                                          io_swap(x[2]), io_swap(x[3]))

    def get_key(x, in_key, len):
        x[4] = x[5] = x[6] = x[7] = 0
        key_words = (len + 63) // 64
        if key_words == 2:
            x[0], x[1], x[2], x[3] = (io_swap(in_key[3]), io_swap(in_key[2]),
                                      io_swap(in_key[1]), io_swap(in_key[0]))
        elif key_words == 3:
            x[0], x[1], x[2], x[3] = (io_swap(in_key[5]), io_swap(in_key[4]),
                                      io_swap(in_key[3]), io_swap(in_key[2]))
            x[4], x[5] = io_swap(in_key[1]), io_swap(in_key[0])
        elif key_words == 4:
            x[0], x[1], x[2], x[3] = (io_swap(in_key[7]), io_swap(in_key[6]),
                                      io_swap(in_key[5]), io_swap(in_key[4]))
            x[4], x[5], x[6], x[7] = (io_swap(in_key[3]), io_swap(in_key[2]),
                                      io_swap(in_key[1]), io_swap(in_key[0]))
else:
    def get_block(x, in_blk):
        x[0], x[1], x[2], x[3] = (io_swap(in_blk[0]), io_swap(in_blk[1]),
                                  io_swap(in_blk[2]), io_swap(in_blk[3]))

    def put_block(x, out_blk):
        out_blk[0], out_blk[1], out_blk[2], out_blk[3] = (io_swap(x[0]), io_swap(x[1]),
                                                          io_swap(x[2]), io_swap(x[3]))

    def get_key(x, in_key, len):
        x[4] = x[5] = x[6] = x[7] = 0
        key_words = (len + 63) // 64
        if key_words >= 2:
            x[0], x[1], x[2], x[3] = (io_swap(in_key[0]), io_swap(in_key[1]),
                                      io_swap(in_key[2]), io_swap(in_key[3]))
        if key_words >= 3:
            x[4], x[5] = io_swap(in_key[4]), io_swap(in_key[5])
        if key_words == 4:
            x[6], x[7] = io_swap(in_key[6]), io_swap(in_key[7])

# Constants
msk = lambda n: ((0x000000ff >> n) * 0x01010101)
brotl = lambda x, n: ((((x) & msk(n)) << (n)) | (((x) & ~msk(n)) >> (8 - (n))))

mb_0 = 0xcffccffc
mb_1 = 0xf33ff33f
mb_2 = 0xfccffccf
mb_3 = 0x3ff33ff3


def row_perm(x):
    return ((x & mb_0) ^
            (rotl(x, 8) & mb_1) ^
            (rotl(x, 16) & mb_2) ^
            (rotl(x, 24) & mb_3))


# More constants
mc0 = 0xacacacac
mc1 = 0x59595959
mc2 = 0xb2b2b2b2
mc3 = 0x65656565

p0 = [15, 14, 10, 1, 11, 5, 8, 13, 9, 3, 2, 7, 0, 6, 4, 12]
p1 = [11, 10, 13, 7, 8, 14, 0, 5, 15, 6, 3, 4, 1, 9, 2, 12]
ip0 = [12, 3, 10, 9, 14, 5, 13, 11, 6, 8, 2, 4, 15, 7, 1, 0]
ip1 = [6, 12, 14, 10, 11, 7, 9, 3, 4, 13, 1, 0, 15, 2, 5, 8]

tab_gen = False
s_box = [[0 for _ in range(256)] for _ in range(4)]
inv_s_tab = [[0] * 256 for _ in range(4)]


def create_inverse_s_tab():
    for i in range(4):
        for j in range(256):
            inv_s_tab[i][s_tab[i][j]] = j


s_tab = [[0 for _ in range(256)] for _ in range(4)]
ce = [0] * 52
cd = [0] * 52

l_key = [0] * 104
e_key = l_key[52:]
d_key = l_key[:52]


def gen_tab():
    global tab_gen, s_box, s_tab, ce, cd

    for i in range(256):
        xl = p1[i >> 4]
        xr = p0[i & 15]

        yl = ((xl & 0x0e) ^ ((xl << 3) & 0x08) ^ ((xl >> 3) & 0x01)
              ^ ((xr << 1) & 0x0a) ^ ((xr << 2) & 0x04)
              ^ ((xr >> 2) & 0x02) ^ ((xr >> 1) & 0x01))

        yr = ((xr & 0x0d) ^ ((xr << 1) & 0x04) ^ ((xr >> 1) & 0x02)
              ^ ((xl >> 1) & 0x05) ^ ((xl << 2) & 0x08)
              ^ ((xl << 1) & 0x02) ^ ((xl >> 2) & 0x01))

        y = ip0[yl] | (ip1[yr] << 4)

        yr = ((y << 3) | (y >> 5)) & 255
        xr = ((i << 3) | (i >> 5)) & 255
        yl = ((y << 1) | (y >> 7)) & 255
        xl = ((i << 1) | (i >> 7)) & 255

        s_box[0][i] = yl
        s_box[1][i] = yr
        s_box[2][xl] = y
        s_box[3][xr] = y

        s_tab[0][i] = (yl * 0x01010101) & 0x3fcff3fc
        s_tab[1][i] = (yr * 0x01010101) & 0xfc3fcff3
        s_tab[2][xl] = (y * 0x01010101) & 0xf3fc3fcf
        s_tab[3][xr] = (y * 0x01010101) & 0xcff3fc3f

    xl = 0xa54ff53a

    for i in range(13):
        ce[4 * i + 0] = xl ^ mc0
        ce[4 * i + 1] = xl ^ mc1
        ce[4 * i + 2] = xl ^ mc2
        ce[4 * i + 3] = xl ^ mc3

        yl = row_perm(rotr(xl, 16) if i & 1 else xl)

        cd[4 * (12 - i) + 0] = yl ^ mc0
        cd[4 * (12 - i) + 1] = rotl(yl, 24) ^ mc1
        cd[4 * (12 - i) + 2] = rotl(yl, 16) ^ mc2
        cd[4 * (12 - i) + 3] = rotl(yl, 8) ^ mc3

        xl = (xl + 0x3c6ef372) & 0xFFFFFFFF

    tab_gen = True


# Constants for key setup
kp = [0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f]
kq = [0x9b05688c, 0x1f83d9ab, 0x5be0cd19, 0xcbbb9d5d]


def h0_block(n, r0, r1):
    global e_key
    e_key[4 * n + 8] = rotl(e_key[4 * n + 0], r0)
    e_key[4 * n + 9] = rc ^ e_key[4 * n + 1]
    e_key[4 * n + 10] = rotl(e_key[4 * n + 2], r1)
    e_key[4 * n + 11] = rc ^ e_key[4 * n + 3]


def h1_block(n, r0, r1):
    global e_key
    e_key[4 * n + 8] = rc ^ e_key[4 * n + 0]
    e_key[4 * n + 9] = rotl(e_key[4 * n + 1], r0)
    e_key[4 * n + 10] = rc ^ e_key[4 * n + 2]
    e_key[4 * n + 11] = rotl(e_key[4 * n + 3], r1)


def set_key(in_key, key_len):
    global e_key, d_key, l_key, tab_gen

    if not tab_gen:
        gen_tab()
        tab_gen = True

    tu = [0] * 4
    tv = [0] * 4

    key_words = (key_len + 63) // 64

    if key_words >= 4:
        tu[3] = in_key[6]
        tv[3] = in_key[7]
    if key_words >= 3:
        tu[2] = in_key[4]
        tv[2] = in_key[5]
    if key_words >= 2:
        tu[0] = in_key[0]
        tv[0] = in_key[1]
        tu[1] = in_key[2]
        tv[1] = in_key[3]

    ek = [0] * 8
    for i in range(4):
        ek[i] = (s_tab[0][byte(tu[0], i)] ^ s_tab[1][byte(tu[1], i)] ^
                 s_tab[2][byte(tu[2], i)] ^ s_tab[3][byte(tu[3], i)])
        ek[i + 4] = (s_tab[2][byte(tv[0], i)] ^ s_tab[3][byte(tv[1], i)] ^
                     s_tab[0][byte(tv[2], i)] ^ s_tab[1][byte(tv[3], i)])

    t0 = ek[0] ^ ek[1] ^ ek[2] ^ ek[3]
    t1 = ek[4] ^ ek[5] ^ ek[6] ^ ek[7]

    for i in range(4):
        ek[i] ^= t1
        ek[i + 4] ^= t0

    for i in range(13):
        for j in range(4):
            e_key[4 * i + j] = ek[j if i % 2 == 0 else j + 4] ^ ce[4 * i + j]

        if i % 2 == 0:
            t = ek[0]
            ek[0] = rotl(ek[1], 24)
            ek[1] = rotl(ek[2], 16)
            ek[2] = brotl(ek[3], 6)
            ek[3] = brotl(t, 6)
        else:
            t = ek[7]
            ek[7] = rotl(ek[6], 16)
            ek[6] = rotl(ek[5], 8)
            ek[5] = brotl(ek[4], 2)
            ek[4] = brotl(t, 2)

    # Set up decryption key schedule
    d_key[0:4] = e_key[48:52]
    for i in range(12):
        d_key[4*i+4:4*i+8] = e_key[44-4*i:48-4*i]
    d_key[48:52] = e_key[0:4]

    # Apply row_perm to the last 4 keys for encryption and first 4 keys for decryption
    for i in range(4):
        e_key[48+i] = row_perm(e_key[48+i])
        d_key[i] = row_perm(d_key[i])

    return l_key


def gamma_tau(i, b, b1, context):
    b1[i] = b[i] ^ setup_key()[i]


def gamma_tau_inverse(i, b, b1, context):
    b1[i] = b[i] ^ setup_key()[i]


def fr0(y, x, i, k):
    return (s_tab[i][byte(x[0], i)] ^
            s_tab[(i + 1) & 3][byte(x[1], i)] ^
            s_tab[(i + 2) & 3][byte(x[2], i)] ^
            s_tab[(i + 3) & 3][byte(x[3], i)] ^ k)


def fr1(y, x, i, k):
    return (s_tab[(i + 2) & 3][byte(x[0], i)] ^
            s_tab[(i + 3) & 3][byte(x[1], i)] ^
            s_tab[i][byte(x[2], i)] ^
            s_tab[(i + 1) & 3][byte(x[3], i)] ^ k)


def f0_rnd(b, kp):
    b1 = [0] * 4
    for i in range(4):
        b1[i] = fr0(b1, b, i, kp[i])
    return b1


def f1_rnd(b, kp):
    b1 = [0] * 4
    for i in range(4):
        b1[i] = fr1(b1, b, i, kp[i])
    return b1


def setup_key():
    return [0x833ab2e7, 0x17289d6e, 0x8dd676d7, 0x30044d10]


def encrypt(plaintext):
    context = setup_key()  # Setting up the key
    b = [int(str(x), 16) if isinstance(x, str) else int(x) for x in plaintext]
    b1 = [0] * 4
    for i in range(4):
        gamma_tau(i, b, b1, context)
    return [hex(x) for x in b1]


def decrypt(ciphertext):
    context = setup_key()  # Setting up the key
    b = [int(x, 16) for x in ciphertext]
    b1 = [0] * 4
    for i in range(4):
        gamma_tau_inverse(i, b, b1, context)
    return [hex(x) for x in b1]


def text_to_blocks(text):
    # Convert text to a list of 32-bit integer blocks
    blocks = []
    for i in range(0, len(text), 4):
        block = 0
        for j in range(4):
            if i + j < len(text):
                block |= ord(text[i + j]) << (j * 8)
        blocks.append(block)
    return blocks


def blocks_to_text(blocks):
    text = ""
    for block in blocks:
        if isinstance(block, str):
            block = int(block, 16)  # Assume the string is a hexadecimal representation
        for i in range(4):  # Assuming 32-bit blocks
            char = (block >> (i * 8)) & 0xff
            if char:
                text += chr(char)
    return text


def encrypt_text(text, key):
    blocks = text_to_blocks(text)
    out_blocks = [0] * len(blocks)
    out_blocks = encrypt(blocks)
    return out_blocks


def decrypt_text(blocks, key):
    out_blocks = [0] * len(blocks)
    out_blocks = decrypt(blocks)
    return blocks_to_text(out_blocks)


# RSA Key Generation
def generate_prime_candidate(length):
    p = random.getrandbits(length)
    while not isprime(p):
        p = random.getrandbits(length)
    return p


def generate_keypair(bits):
    p = generate_prime_candidate(bits)
    q = generate_prime_candidate(bits)
    while p == q:
        p = generate_prime_candidate(bits)
        q = generate_prime_candidate(bits)
    n = p * q
    phi = (p - 1) * (q - 1)

    e = random.randrange(1, phi)
    g = gcd(e, phi)
    while g != 1:
        e = random.randrange(1, phi)
        g = gcd(e, phi)

    d = modinv(e, phi)
    return (e, n), (d, n)


def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a


def modinv(a, m):
    m0, x0, x1 = m, 0, 1
    while a > 1:
        q = a // m
        m, a = a % m, m
        x0, x1 = x1 - q * x0, x0
    return x1 + m0 if x1 < 0 else x1


# RSA Encryption and Decryption
def rsa_encrypt(plaintext, public_key):
    e, n = public_key
    encrypted = [pow(ord(char), e, n) for char in plaintext]
    return encrypted


def rsa_decrypt(ciphertext, private_key):
    d, n = private_key
    decrypted = ''.join([chr(pow(char, d, n)) for char in ciphertext])
    return decrypted


# Rabin Key Generation
def rabin_generate_keypair(bits):
    p = generate_prime_candidate(bits)
    q = generate_prime_candidate(bits)
    n = p * q
    return p, q, n


# Rabin Signature and Verification
def rabin_sign(message, p, q):
    n = p * q
    hashed_message = hash(message) % n
    signature = pow(hashed_message, 2, n)
    return signature


def rabin_verify(message, signature, n):
    hashed_message = hash(message) % n
    return pow(signature, 1, n) == pow(hashed_message, 2, n)

# Example usage:
if __name__ == "__main__":
    # Testing encryption and decryption
    plaintext = "Hello there Bob!"
    print(f"Plaintext:, {plaintext}")
    key = setup_key()
    print(f"Key:  {key}")
    # RSA Key Pair Generation
    public_key, private_key = generate_keypair(8)

    # Rabin Key Pair Generation
    p, q, n = rabin_generate_keypair(8)
    rabin_message = plaintext

    # Signing the message with Rabin Signature
    rabin_signature = rabin_sign(rabin_message, p, q)

    # encrypt the text using CRYPTON
    ciphertext = encrypt_text(plaintext, key)

    # Encrypt the CRYPTON key using RSA Public Key
    rsa_key_ciphertext = rsa_encrypt(str(key), public_key)

    print(f"\nCiphertext: {ciphertext}")
    print(f"RSA Encrypted Key: {rsa_key_ciphertext}")

    # Decrypting the CRYPTON key using RSA Private Key
    rsa_decrypted_key = rsa_decrypt(rsa_key_ciphertext, private_key)

    # Decrypting the text using CRYPTON
    decrypted = decrypt_text(ciphertext, rsa_decrypted_key)

    # Verifying the message using Rabin Signature
    is_valid = rabin_verify(rabin_message, rabin_signature, n)

    print(f"\nRabin Message: {rabin_message}")
    print(f"Rabin Signature: {rabin_signature}")
    print(f"Rabin Signature Valid: {is_valid}")

    print(f"\nDecrypted message: {decrypted}")

    if plaintext == decrypted:
        print("\n\nEncryption and decryption successful!")
    else:
        print("Decryption failed")
        print("Original:", plaintext)
        print("Decrypted:", decrypted)
