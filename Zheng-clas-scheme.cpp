extern "C" {
#include "miracl.h"
}
#include <cstdio>
#include <ctime>
#include "big.h"
#include "ecn.h"
#include <openssl/sha.h>
#include <sstream>
#include <vector>

Big randbits(int n) { Big z; bigbits(n, z.fn); return z; }
Miracl precision(196, 16);
miracl* mip = &precision;
ECn g, Pub;
Big q, alpha;
#define HASH_LEN 32


struct Sig
{
    ECn U;
    Big s;
};

struct PK {
    ECn X;
    ECn R;
};

struct SK {
    Big x;
    Big d;
};

struct PID
{
    ECn pid1;
    Big pid2;
    long T;
};

void setup();
Big Hash(stringstream& st);

class Clas {
private:
public:
    virtual void reg() = 0;
    virtual Sig& sign(string& m) = 0;
    virtual PK& getPK() = 0;
    virtual ECn& getPub() = 0;
};

//! NIST p192 bits ECC curve prime
char* ecp = (char*)"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF";

//! NIST p192 bits ECC curve parameter b
char* ecb = (char*)"64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1";

//! NIST p192 bits ECC curve parameter q
char* ecq = (char*)"FFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831";

//! NIST p192 bits ECC curve point of prime order (x,y)
char* ecx = (char*)"188DA80EB03090F67CBF20EB43A18800F4FF0AFD82FF1012";
char* ecy = (char*)"07192B95FFC8DA78631011ED6B24CDD573F977A11E794811";

class OurCLAS : public Clas {
public:
    virtual void reg() {
        sk.x = rand(q);
        Big r = rand(q);
        pk.X = sk.x * g, pk.R = r * g;
        pid = PID{ rand(q) * g, randbits(256), clock()};

        st << pid.pid1 << pid.pid2 << pid.T << pk.R << Pub;
        Big h1 = Hash(st);
        sk.d = r + alpha * h1;


    }

    PK& getPK() {
        return pk;
    }

    PID& getPID() {
        return pid;
    }

    long getTimestamp() {
        return t;
    }

    ECn& getPub() {
        return Pub;
    }

    virtual Sig& sign(string& m) {
        Big u = rand(q);//random value
        ECn U = u * g;
        t = clock();//timestamp

        st << pid.pid1 << pid.pid2 << pid.T << pk.X << Pub << pk.R << t;
        Big h2 = Hash(st);
        st << pid.pid1 << pid.pid2 << pid.T << m << pk.X << pk.R << U << t;
        Big h3 = Hash(st);

        sig.s = u + sk.d * h2 + sk.x * h3;
        sig.U = U;
        return sig;
    }

private:
    PK pk;
    SK sk;
    Sig sig;
    stringstream st;
    long t = 1;
    PID pid;
};

void setup() {
    // Elliptic curve parameter reading
    Big a, b, p, px, py;
    int bits;
    a = -3;
    mip->IOBASE = 16;
    b = ecb;
    p = ecp;
    q = ecq;
    px = ecx;
    py = ecy;
    ecurve(a, b, p, MR_BEST);
    g = ECn(px, py);//generator
    alpha = rand(q);
    Pub = alpha * g;
}

Big Hash(stringstream& st) {
    size_t size = st.tellp();
    char* buff = new char[size];
    st.read(buff, size);
    unsigned char value[HASH_LEN];
    SHA256((unsigned char*)buff, size, value);
    st.str("");
    delete[] buff;
    return from_binary(HASH_LEN, (char*)value);
}

bool verify(Sig& sig, PID& pid, PK& pk, ECn& Pub, string& m, long timestp) {
    stringstream st;
    ECn left, right;
    st << pid.pid1 << pid.pid2 << pid.T << pk.R << Pub;
    Big h1 = Hash(st);
    st << pid.pid1 << pid.pid2 << pid.T << pk.X << Pub << pk.R << timestp;
    Big h2 = Hash(st);
    st << pid.pid1 << pid.pid2 << pid.T << m << pk.X << pk.R << sig.U <<timestp;
    Big h3 = Hash(st);
    left = sig.s * g;
    right = h1 * Pub;
    right += pk.R;
    right *= h2;
    right += h3 * pk.X;
    right += sig.U;
    if (left == right) {
        return true;
    }
    return false;
}

bool aggVerify(int n, string& msg, Big& aggSig, vector<PID>& vecPID, vector<PK>& vecPK, vector<ECn>& vecU, vector<long>& vecT) {
    ECn right, r1, r2, r3, temp;
    stringstream st;
    ECn left = aggSig * g;
    for (int i = 0; i < n; i++) {
        st << vecPID[i].pid1 << vecPID[i].pid2 << vecPID[i].T << vecPK[i].R << Pub;
        Big h1 = Hash(st);
        st << vecPID[i].pid1 << vecPID[i].pid2 << vecPID[i].T << vecPK[i].X << Pub << vecPK[i].R << vecT[i];
        Big h2 = Hash(st);
        st << vecPID[i].pid1 << vecPID[i].pid2 << vecPID[i].T << msg << vecPK[i].X << vecPK[i].R << vecU[i] << vecT[i];
        Big h3 = Hash(st);

        r1 += vecU[i];

        temp = h1 * Pub;
        temp += vecPK[i].R;
        temp *= h2;
        r2 += temp;

        r3 += h3 * vecPK[i].X;
    }
    right += r1;
    right += r2;
    right += r3;
    if (left == right) {
        return true;
    }
    return false;
}

void singleTest(OurCLAS& clas) {
    double start;
    double diff;
    Sig sig;
    ECn left, right;
    string msg("This is a test.");
    cout << "First, we generate public key and scret key!" << endl;

    clas.reg();

    cout << "\nThen we compute the signature." << endl;
    start = clock();
    sig = clas.sign(msg);
    diff = ((double)clock() - start) / CLOCKS_PER_SEC * 1000.0;
    cout << "Sig: {" << sig.U << ", " << sig.s << "}" << endl;
    printf("[*] Sign Time: %.6fms\n", diff);

    cout << "\nNow, we start to verify the sig." << endl;
    start = clock();
    if (verify(sig, clas.getPID(), clas.getPK(), clas.getPub(), msg, clas.getTimestamp())) {
        diff = ((double)clock() - start) / CLOCKS_PER_SEC * 1000.0;
        printf("[*] ACCEPT! Verification Time: %.6fms\n", diff);
    }
}

void avgTest(OurCLAS& clas, int n) {
    double s_start, v_start, s_total = 0, v_total = 0;
    Sig sig;
    ECn left, right;
    string msg("A traffic accident occurred 100 meters ahead.");
    for (int i = 0; i < n; i++) {
        clas.reg();
        s_start = clock();
        sig = clas.sign(msg);
        s_total += clock() - s_start;
        v_start = clock();
        if (verify(sig, clas.getPID(), clas.getPK(), clas.getPub(), msg, clas.getTimestamp())) {
            v_total += clock() - v_start;
        }
        else {
            cout << "[x] verification reject!" << endl;
            exit(-1);
        }
    }
    printf("[*] Average Signing Time: %.6fms\n", s_total / n / CLOCKS_PER_SEC * 1000.0);
    printf("[*] Average Individual Verification Time: %.6fms\n", v_total / n / CLOCKS_PER_SEC * 1000.0);
}

void aggTest(OurCLAS& ourclas, int n) {
    string msg("This is a test.");
    vector<ECn> vecU;
    vector<PID> vecPID;
    vector<PK> vecPK;
    vector<long> vecT;
    Big aggSig(0);
    for (int i = 0; i < n; i++) {
        ourclas.reg();
        Sig sig = ourclas.sign(msg);
        aggSig += sig.s;
        vecU.push_back(sig.U);
        vecPID.push_back(ourclas.getPID());
        vecPK.push_back(ourclas.getPK());
        vecT.push_back(ourclas.getTimestamp());
    }
    double start = clock();
    if (aggVerify(n, msg, aggSig, vecPID, vecPK, vecU, vecT)) {
        double end = clock();
        printf("[*] %d Aggregate Verification Time: %.6fms\n", n, (end - start) / CLOCKS_PER_SEC * 1000.0);
    }
}

int main() {
    irand(2022l); // Set random seeds
    setup();
    cout << endl << "------------Zheng-------------" << endl;
    OurCLAS ourclas;
    //singleTest(ourclas);
    avgTest(ourclas, 1000);//average signle signature&verfication excution time
    aggTest(ourclas, 100);//average aggregate signature verfication excution time
    aggTest(ourclas, 200);
    aggTest(ourclas, 300);
    aggTest(ourclas, 400);
    aggTest(ourclas, 500);
    return 0;
}