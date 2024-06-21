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
    Big T;
};

struct PSEU
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

class CLAS : public Clas {
public:
    virtual void reg() {
        usk = rand(q);
        Big a = rand(q);
        upk = usk * Pub;
        ECn A = a * g;

        pseu = PSEU{ rand(q) * g, randbits(256), clock() };

        st << A << pseu.pid1 << pseu.pid2 << pseu.T;
        Big h1 = Hash(st);

        ppk = a + alpha * h1;
        st << pseu.pid1 << pseu.pid2 << pseu.T << upk;
        Big h2 = Hash(st);
        F = ppk * Pub;
        F += h2 * upk;

    }

    PSEU& getPSEU() {
        return pseu;
    }

    long getTimestamp() {
        return t;
    }

    ECn& getupk() {
        return upk;
    }

    ECn& getF() {
        return F;
    }

    ECn& getPub() {
        return Pub;
    }

    virtual Sig& sign(string& m) {
        Big u = rand(q);//random value
        sig.U = u * Pub;
        t = clock();//timestamp

        st << pseu.pid1 << pseu.pid2 << pseu.T << upk;
        Big h2 = Hash(st);
        st << m << pseu.pid1 << pseu.pid2 << pseu.T << sig.U << t;
        Big h3 = Hash(st);

        sig.T = h3 * ( ppk + h2 * usk ) + u;

        return sig;
    }

private:
    Big usk,ppk;
    Sig sig;
    ECn upk,F;
    stringstream st;
    long t = 1;
    PSEU pseu;
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

bool verify(Sig& sig, PSEU& pseu, ECn& upk, ECn&F, ECn& Pub, string& m, long timestp) {
    stringstream st;
    ECn left, right;
    st << m << pseu.pid1 << pseu.pid2 << pseu.T << sig.U << timestp;
    Big h3 = Hash(st);

    left = sig.T * Pub;
    
    right = h3 * F;
    right += sig.U;

    if (left == right) {
        return true;
    }
    return false;
}

bool aggVerify(int n, Big v, Big h4verify, string& msg, Big& aggSig, vector<Sig>& vecsig, vector<PSEU>& vecPSEU, vector<ECn>& vecF,  vector<ECn>& vecupk, vector<long>& vecT) {
    ECn right, r1, temp;
    stringstream st,sth4;
    ECn left = aggSig * Pub;
    for (int i = 0; i < n; i++) {
        st << msg << vecPSEU[i].pid1 << vecPSEU[i].pid2 << vecPSEU[i].T << vecsig[i].U << vecT[i];
        Big h3 = Hash(st);

        temp = h3 * vecF[i];
        temp += vecsig[i].U;
        sth4 << v*temp;

        r1 = h3 * vecF[i];
        r1 += vecsig[i].U;
        right += r1;

    }

    Big h4 = Hash(sth4);

    if (left == right && h4verify==h4) {
        return true;
    }
    return false;
}

void singleTest(CLAS& clas) {
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
    cout << "Sig: {" << sig.U << ", " << sig.T << "}" << endl;
    printf("[*] Sign Time: %.6fms\n", diff);

    cout << "\nNow, we start to verify the sig." << endl;
    start = clock();
    if (verify(sig, clas.getPSEU(), clas.getupk(), clas.getF(), clas.getPub(), msg, clas.getTimestamp())) {
        diff = ((double)clock() - start) / CLOCKS_PER_SEC * 1000.0;
        printf("[*] ACCEPT! Verification Time: %.6fms\n", diff);
    }
}

void avgTest(CLAS& clas, int n) {
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
        if (verify(sig, clas.getPSEU(), clas.getupk(), clas.getF(), clas.getPub(), msg, clas.getTimestamp())) {
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

void aggTest(CLAS& xiong, int n) {
    string msg("This is a test.");
    vector<Sig> vecsig;
    vector<PSEU> vecPSEU;
    vector<ECn> vecF;
    vector<ECn> vecupk;
    vector<long> vecT;
    stringstream st;
    Big aggSig(0);
    Big v = rand(q);
    ECn pk = v * Pub;
    for (int i = 0; i < n; i++) {
        xiong.reg();
        Sig sig = xiong.sign(msg);
        st << sig.T * pk;
        aggSig += sig.T;
        vecsig.push_back(sig);
        vecPSEU.push_back(xiong.getPSEU());
        vecF.push_back(xiong.getF());
        vecupk.push_back(xiong.getupk());
        vecT.push_back(xiong.getTimestamp());
    }
    Big h4 = Hash(st);
    double start = clock();
    if (aggVerify(n, v, h4, msg, aggSig, vecsig, vecPSEU, vecF, vecupk, vecT)) {
        double end = clock();
        printf("[*] %d Aggregate Verification Time: %.6fms\n", n, (end - start) / CLOCKS_PER_SEC * 1000.0);
    }
}

int main() {
    irand(2022l); // Set random seeds
    setup();
    cout << endl << "------------Xiong-------------" << endl;
    CLAS xiong;
    //singleTest(xiong);
    avgTest(xiong, 1000);//average signle signature&verfication excution time
    aggTest(xiong, 100);//average aggregate signature verfication excution time
    aggTest(xiong, 200);
    aggTest(xiong, 300);
    aggTest(xiong, 400);
    aggTest(xiong, 500);
    return 0;
}