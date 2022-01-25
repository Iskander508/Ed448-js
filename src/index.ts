import { BigInteger } from "jsbn";
import jsSHA from "jssha";

function shake256(content: number[], outputBytes: number): number[] {
  const shaObj = new jsSHA("SHAKE256", "UINT8ARRAY");
  shaObj.update(Uint8Array.from(content));
  return Array.from(
    shaObj.getHash("UINT8ARRAY", { outputLen: outputBytes * 8 }),
  );
}

function fromNumber(x: number): BigInteger {
  return new BigInteger(x.toString(10));
}

const N0 = BigInteger.ZERO;
const N1 = BigInteger.ONE;
const N2 = fromNumber(2);
const N3 = fromNumber(3);
const N4 = fromNumber(4);
const N5 = fromNumber(5);
const N8 = fromNumber(8);

function truediv(x: number, y: number): number {
  return Math.floor(x / y);
}

function tobytes(x: BigInteger, b: number): number[] {
  const bytes = truediv(b, 8);
  const arr = x
    .toByteArray()
    .slice(0, bytes)
    .map(x => (x >= 0 ? x : x + 0x100));

  const length = arr.length;
  if (length < bytes) {
    arr.unshift(...Array.from({ length: bytes - length }, () => 0));
  }
  return arr.reverse(); // little endian
}

// Implementation based on https://datatracker.ietf.org/doc/html/rfc8032#appendix-A

function sqrt4k3(x: BigInteger, p: BigInteger): BigInteger {
  // pow(x,(p + 1)//4,p)
  return x.modPow(p.add(N1).divide(N4), p);
}

function sqrt8k5(x: BigInteger, p: BigInteger): BigInteger {
  // y = pow(x,(p+3)//8,p)
  // #If the square root exists, it is either y or y*2^(p-1)/4.
  // if (y * y) % p == x % p: return y
  // else:
  //     z = pow(2,(p - 1)//4,p)
  //     return (y * z) % p
  const y = x.modPow(p.add(N3).divide(N8), p);
  if (
    y
      .multiply(y)
      .mod(p)
      .compareTo(x.mod(p)) === 0
  ) {
    return y;
  } else {
    const z = N2.modPow(p.subtract(N1).divide(N4), p);
    return y.multiply(z).mod(p);
  }
}

function hexi(s: string): BigInteger {
  return new BigInteger(s, 16);
}

function from_le(s: number[]): BigInteger {
  return new BigInteger(
    Buffer.from(s)
      .reverse()
      .toString("hex"),
    16,
  );
}

class Field {
  readonly X: BigInteger;
  readonly P: BigInteger;
  constructor(x: BigInteger, p: BigInteger) {
    this.X = x.mod(p);
    this.P = p;
  }

  // __check_fields
  private check_fields(y: Field): void {
    if (y.P.compareTo(this.P) !== 0) {
      throw new Error("Fields don't match");
    }
  }

  // __add__
  add(y: Field): Field {
    this.check_fields(y);
    return new Field(this.X.add(y.X), this.P);
  }

  // __sub__
  sub(y: Field): Field {
    this.check_fields(y);
    return new Field(this.X.subtract(y.X), this.P);
  }

  // __neg__
  neg(): Field {
    return new Field(this.P.subtract(this.X), this.P);
  }

  // __mul__
  mul(y: Field): Field {
    this.check_fields(y);
    return new Field(this.X.multiply(y.X), this.P);
  }

  // __truediv__
  div(y: Field): Field {
    return this.mul(y.inv());
  }

  inv(): Field {
    const x = this.X.modPow(this.P.subtract(N2), this.P);
    return new Field(x, this.P);
  }

  sqrt(): Field | null {
    let y: BigInteger;
    if (this.P.mod(N4).compareTo(N3) === 0) {
      y = sqrt4k3(this.X, this.P);
    } else if (this.P.mod(N8).compareTo(N5) === 0) {
      y = sqrt8k5(this.X, this.P);
    } else {
      throw new Error("NotImplementedError('sqrt(_,8k+1)')");
    }

    const _y = new Field(y, this.P);
    if (_y.mul(_y).equals(this)) {
      return _y;
    } else {
      return null;
    }
  }

  make(ival: BigInteger): Field {
    return new Field(ival, this.P);
  }

  iszero(): boolean {
    return this.X.compareTo(N0) === 0;
  }

  // __eq__
  equals(y: Field): boolean {
    return !this.X.compareTo(y.X) && !this.P.compareTo(y.P);
  }

  tobytes(b: number): number[] {
    return tobytes(this.X, b);
  }

  frombytes(x: number[], b: number): Field | null {
    const rv = from_le(x).mod(N2.pow(b - 1));
    if (rv.compareTo(this.P) < 0) {
      return new Field(rv, this.P);
    } else {
      return null;
    }
  }

  sign(): number {
    return this.X.mod(N2).intValue();
  }
}
abstract class EdwardsPoint {
  readonly baseField: Field;
  X: Field;
  Y: Field;
  Z: Field;

  constructor(baseField: Field, x: Field, y: Field) {
    this.baseField = baseField;
    this.X = x;
    this.Y = y;
    this.Z = baseField.make(N1);
  }

  abstract solve_x2(y: Field): Field;
  abstract zero_element(): EdwardsPoint;
  abstract l(): BigInteger;
  abstract n(): number;
  abstract b(): number;
  abstract c(): number;
  abstract double(): EdwardsPoint;
  abstract add(y: EdwardsPoint): EdwardsPoint;
  abstract encode(): number[];
  abstract decode(s: number[]): EdwardsPoint | null;

  protected decode_base(s: number[], b: number): [Field | null, Field | null] {
    if (s.length !== truediv(b, 8)) {
      return [null, null];
    }
    const xs = s[truediv(b - 1, 8)] >> ((b - 1) & 7);
    const y = this.baseField.frombytes(s, b);
    if (!y) {
      return [null, null];
    }
    let x = this.solve_x2(y).sqrt();
    if (!x || (x.iszero() && xs !== x.sign())) {
      return [null, null];
    }
    if (x.sign() !== xs) {
      x = x.neg();
    }
    return [x, y];
  }

  protected encode_base(b: number): number[] {
    const xp = this.X.div(this.Z);
    const yp = this.Y.div(this.Z);
    const s = yp.tobytes(b);
    if (xp.sign() !== 0) {
      s[truediv(b - 1, 8)] |= 1 << (b - 1) % 8;
    }
    return s;
  }

  // __mul__
  mul(x: BigInteger): EdwardsPoint {
    let r = this.zero_element();
    let s = this as EdwardsPoint;
    while (x.compareTo(N0) > 0) {
      if (x.mod(N2).compareTo(N0) > 0) {
        r = r.add(s);
      }
      s = s.double();
      x = x.divide(N2);
    }
    return r;
  }

  // __eq__
  equals(y: EdwardsPoint): boolean {
    const xn1 = this.X.mul(y.Z);
    const xn2 = y.X.mul(this.Z);
    const yn1 = this.Y.mul(y.Z);
    const yn2 = y.Y.mul(this.Z);
    return xn1.equals(xn2) && yn1.equals(yn2);
  }
}

class Edwards448Point extends EdwardsPoint {
  // P = 2 ** 448 - 2 ** 224 - 1
  static readonly P = new BigInteger(
    "726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439",
  );

  static readonly L = hexi(
    "3fffffffffffffffffffffffffffffffffffffffffffffffffffffff7cca23e9c44edb49aed63690216cc2728dc58f552378c292ab5844f3",
  );
  static readonly C = 2;
  static readonly N = 447;
  static readonly B = 456;

  static readonly baseField = new Field(N1, Edwards448Point.P);
  static readonly D = Edwards448Point.baseField.make(fromNumber(-39081));
  static readonly F0 = Edwards448Point.baseField.make(N0);
  static readonly F1 = Edwards448Point.baseField.make(N1);
  static readonly XB = Edwards448Point.baseField.make(
    hexi(
      "4F1970C66BED0DED221D15A622BF36DA9E146570470F1767EA6DE324A3D3A46412AE1AF72AB66511433B80E18B00938E2626A82BC70CC05E",
    ),
  );
  static readonly YB = Edwards448Point.baseField.make(
    hexi(
      "693F46716EB6BC248876203756C9C7624BEA73736CA3984087789C1E05A0C2D73AD3FF1CE67C39C4FDBD132C4ED7C8AD9808795BF230FA14",
    ),
  );

  constructor(x: Field, y: Field) {
    if (
      !y
        .mul(y)
        .add(x.mul(x))
        .equals(
          Edwards448Point.F1.add(
            Edwards448Point.D.mul(x)
              .mul(x)
              .mul(y)
              .mul(y),
          ),
        )
    ) {
      throw new Error("Invalid point");
    }

    super(Edwards448Point.baseField, x, y);
  }

  static stdbase(): EdwardsPoint {
    return new Edwards448Point(Edwards448Point.XB, Edwards448Point.YB);
  }

  decode(s: number[]): EdwardsPoint | null {
    const [x, y] = this.decode_base(s, 456);
    if (x === null || y === null) {
      return null;
    }
    return new Edwards448Point(x, y);
  }

  encode(): number[] {
    return this.encode_base(456);
  }

  zero_element() {
    return new Edwards448Point(Edwards448Point.F0, Edwards448Point.F1);
  }

  solve_x2(y: Field): Field {
    return y
      .mul(y)
      .sub(Edwards448Point.F1)
      .div(
        Edwards448Point.D.mul(y)
          .mul(y)
          .sub(Edwards448Point.F1),
      );
  }

  // __add__
  add(y: EdwardsPoint) {
    const tmp = this.zero_element();
    const xcp = this.X.mul(y.X);
    const ycp = this.Y.mul(y.Y);
    const zcp = this.Z.mul(y.Z);
    const B = zcp.mul(zcp);
    const E = Edwards448Point.D.mul(xcp).mul(ycp);
    const F = B.sub(E);
    const G = B.add(E);
    tmp.X = zcp.mul(F).mul(
      this.X.add(this.Y)
        .mul(y.X.add(y.Y))
        .sub(xcp)
        .sub(ycp),
    );
    tmp.Y = zcp.mul(G).mul(ycp.sub(xcp));
    tmp.Z = F.mul(G);
    return tmp;
  }

  double(): EdwardsPoint {
    const tmp = this.zero_element();
    const x1s = this.X.mul(this.X);
    const y1s = this.Y.mul(this.Y);
    const z1s = this.Z.mul(this.Z);
    const xys = this.X.add(this.Y);
    const F = x1s.add(y1s);
    const J = F.sub(z1s.add(z1s));
    tmp.X = xys
      .mul(xys)
      .sub(x1s)
      .sub(y1s)
      .mul(J);
    tmp.Y = F.mul(x1s.sub(y1s));
    tmp.Z = F.mul(J);
    return tmp;
  }

  l() {
    return Edwards448Point.L;
  }
  n() {
    return Edwards448Point.N;
  }
  b() {
    return Edwards448Point.B;
  }
  c() {
    return Edwards448Point.C;
  }
}

type HashFunction = (
  data: number[],
  ctx: null | number[],
  hflag: boolean,
) => number[];

class PureEdDSA {
  private readonly B: EdwardsPoint;
  private readonly H: HashFunction;
  private readonly l: BigInteger;
  private readonly n: number;
  private readonly b: number;
  private readonly c: number;
  constructor(B: EdwardsPoint, H: HashFunction) {
    this.B = B;
    this.H = H;
    this.l = B.l();
    this.n = B.n();
    this.b = B.b();
    this.c = B.c();
  }

  private clamp(a: number[]): number[] {
    const _a = [...a];
    for (let i = 0; i < this.c; ++i) {
      _a[truediv(i, 8)] &= ~(1 << i % 8);
    }
    _a[truediv(this.n, 8)] |= 1 << this.n % 8;
    for (let i = this.n + 1; i < this.b; ++i) {
      _a[truediv(i, 8)] &= ~(1 << i % 8);
    }
    return _a;
  }

  keygen(privkey: number[]): number[] {
    if (privkey.length !== truediv(this.b, 8)) {
      throw new Error(`Invalid private key length: ${privkey.length} `);
    }

    const khash = this.H(privkey, null, false);
    const a = from_le(this.clamp(khash.slice(0, truediv(this.b, 8))));
    return this.B.mul(a).encode();
  }

  sign(
    privkey: number[],
    pubkey: number[],
    msg: number[],
    ctx: null | number[],
    hflag: boolean,
  ): number[] {
    if (privkey.length !== truediv(this.b, 8)) {
      throw new Error(`Invalid private key length: ${privkey.length} `);
    }
    if (pubkey.length !== truediv(this.b, 8)) {
      throw new Error(`Invalid public key length: ${pubkey.length} `);
    }
    if (!msg) {
      throw new Error("Missing message input");
    }

    const khash = this.H(privkey, null, false);
    const a = from_le(this.clamp(khash.slice(0, truediv(this.b, 8))));
    const seed = khash.slice(truediv(this.b, 8));
    const r = from_le(this.H(seed.concat(msg), ctx, hflag)).mod(this.l);
    const R = this.B.mul(r).encode();
    const h = from_le(this.H(R.concat(pubkey).concat(msg), ctx, hflag)).mod(
      this.l,
    );
    const S = tobytes(r.add(h.multiply(a)).mod(this.l), this.b);
    return R.concat(S);
  }

  verify(
    pubkey: number[],
    msg: number[],
    sig: number[],
    ctx: null | number[],
    hflag: boolean,
  ): boolean {
    if (sig.length !== truediv(this.b, 4)) {
      return false;
    }
    if (pubkey.length !== truediv(this.b, 8)) {
      return false;
    }

    const Rraw = sig.slice(0, truediv(this.b, 8));
    const Sraw = sig.slice(truediv(this.b, 8));
    const R = this.B.decode(Rraw);
    const S = from_le(Sraw);
    const A = this.B.decode(pubkey);
    if (!R || !A || S.compareTo(this.l) >= 0) {
      return false;
    }

    const h = from_le(this.H(Rraw.concat(pubkey).concat(msg), ctx, hflag)).mod(
      this.l,
    );
    let rhs = R.add(A.mul(h));
    let lhs = this.B.mul(S);
    for (let i = 0; i < this.c; ++i) {
      lhs = lhs.double();
      rhs = rhs.double();
    }
    return lhs.equals(rhs);
  }
}

type Input = number[] | Uint8Array | Buffer;

export interface EdDSA {
  getPublicKey(privateKey: Input): number[];

  sign(
    privateKey: Input,
    publicKey: Input,
    data: Input,
    context?: null | Input,
  ): number[];

  verify(
    publicKey: Input,
    data: Input,
    signature: Input,
    context?: null | Input,
  ): boolean;
}

class EdDSAImpl implements EdDSA {
  private readonly pure: PureEdDSA;
  private readonly pflag = false;
  constructor(pureScheme: PureEdDSA) {
    this.pure = pureScheme;
  }

  getPublicKey(privateKey: Input) {
    return this.pure.keygen(Array.from(privateKey));
  }

  sign(
    privateKey: Input,
    publicKey: Input,
    data: Input,
    context: null | Input = null,
  ) {
    return this.pure.sign(
      Array.from(privateKey),
      Array.from(publicKey),
      Array.from(data),
      context ? Array.from(context) : [],
      this.pflag,
    );
  }

  verify(
    publicKey: Input,
    data: Input,
    signature: Input,
    context: null | Input = null,
  ) {
    return this.pure.verify(
      Array.from(publicKey),
      Array.from(data),
      Array.from(signature),
      context ? Array.from(context) : [],
      this.pflag,
    );
  }
}

const SignatureTitle = Array.from(Buffer.from("SigEd448", "utf8"));
function Ed448_inthash(
  data: number[],
  ctx: null | number[],
  hflag: boolean,
): number[] {
  const dompfx: number[] = [];
  if (ctx) {
    if (ctx.length > 255) {
      throw new Error("Context too big");
    }
    dompfx.push(
      ...SignatureTitle.concat([hflag ? 1 : 0, ctx.length]).concat(ctx),
    );
  }

  return shake256(dompfx.concat(data), 114);
}

export default function createEd448(): EdDSA {
  const pEd448 = new PureEdDSA(Edwards448Point.stdbase(), Ed448_inthash);
  return new EdDSAImpl(pEd448);
}
