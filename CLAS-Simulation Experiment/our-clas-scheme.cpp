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

//extern Miracl precision;
//extern ECn g, Pub;
//extern Big q, alpha;


struct Sig
{
    ECn U;
    Big s;
};

struct PID
{
    Big AID;
    long T;
};

void setup();
Big Hash(stringstream& st);

class Clas {
private:
public:
    virtual void reg() = 0;
    virtual Big& sign(string& m) = 0;
    virtual ECn& getpk() = 0;
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
    virtual void reg() {//regenerate the private key, public key, PID 
        x = rand(q);
        Big r = rand(q);
        u = rand(q);//random value
        U = u * g;
        pid = PID{ randbits(256), clock() };
        X = x * g;
        R = r * g;

        st << pid.AID << pid.T << X << R;
        // h2_struct = H2{pid, pk.R, X};      
        Big h2 = Hash(st);
        pk = h2 * X;
        pk += R;//generate PK        

        // cout << "PK: {" << pk.X << ", " << pk.R << "}" << endl;
        st << pid.AID << pid.T << pk << Pub;
        // h1_struct = H1{pid, Q, pk.R, Pub};        
        Big h1 = Hash(st);
        psk = r + alpha * h1;//generate psk
        sk = psk + h2 * x;
        // cout << "sk: {" << sk.x << ", " << sk.d << "}" << endl;

    }

    ECn& getpk() {
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

    ECn& getX() {
        return X;
    }

    ECn& getU() {
        return U;
    }

    virtual Big& sign(string& m) {

        t = clock();//timestamp
        // h2_struct = H2{pid, pk, U, t};
        // h3_struct = H3{pid, U};
        st << pid.AID << pid.T << X << R;
        Big h2 = Hash(st);
        st << pid.AID << pid.T << pk << U << m << t;
        Big h3 = Hash(st);

        sig = u + h3 * sk;
        return sig;
    }

private:
    ECn pk,R,X,U;
    Big u,x,sk,psk;
    Big sig;
    stringstream st;
    long t = 1;
    PID pid;
};

void setup() {
    // 椭圆曲线参数读入
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
    g = ECn(px, py);            //生成元
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

bool verify(Big& sig, PID& pid, ECn& pk, ECn& U, ECn& Pub, string& m, long timestp) {
    // suppose we have received PID, PK, T, m and s
    stringstream st;
    ECn left, right;
    st << pid.AID << pid.T << pk << Pub;
    Big h1 = Hash(st);
    st << pid.AID << pid.T << pk << U << m << timestp;
    Big h3 = Hash(st);

    left = sig * g;
    right = h1 * Pub;
    right += pk;
    right *= h3;
    right += U;
    // cout << left << endl << right << endl;
    if (left == right) {
        return true;
    }
    return false;
}

bool aggVerify(int n, string& msg, ECn& aggSig, Big& h4, vector<PID>& vecPID, vector<ECn>& vecPK, vector<ECn>& vecU, vector<long>& vecT) {
    ECn right, r1, r2, temp;
    Big r3;
    stringstream sth1,sth4;
    ECn left = aggSig;
    for (int i = 0; i < n; i++) {
        sth1 << vecPID[i].AID << vecPID[i].T << vecPK[i] << Pub;
        Big h1 = Hash(sth1);
       
        temp = h1 * Pub;
        temp += vecPK[i];
        sth4 << temp;

        right += temp;
    }

    Big vh4 = Hash(sth4);

    if (left == right && h4==vh4) {
        return true;
    }
    return false;
}

void singleTest(OurCLAS& clas) {
    double start;
    double diff;
    Big sig;
    ECn left, right;
    string msg("This is a test.");
    cout << "First, we generate public key and scret key!" << endl;

    clas.reg();

    cout << "\nThen we compute the signature." << endl;
    start = clock();
    sig = clas.sign(msg);
    diff = ((double)clock() - start) / CLOCKS_PER_SEC * 1000.0;
    cout << "Sig: {" << clas.getU() << ", " << sig << "}" << endl;
    printf("[*] Sign Time: %.6fms\n", diff);

    cout << "\nNow, we start to verify the sig." << endl;
    start = clock();
    if (verify(sig, clas.getPID(), clas.getpk(), clas.getPub(), clas.getU(), msg, clas.getTimestamp())) {
        diff = ((double)clock() - start) / CLOCKS_PER_SEC * 1000.0;
        printf("[*] ACCEPT! Verification Time: %.6fms\n", diff);
    }
}

void avgTest(OurCLAS& clas, int n) {
    double s_start=0, v_start=0, s_total = 0, v_total = 0;
    Big sig;
    ECn left, right;
    string msg("A traffic accident occurred 100 meters ahead.");
    for (int i = 0; i < n; i++) {
        clas.reg();
        s_start = clock();
        sig = clas.sign(msg);
        s_total += clock() - s_start;
        v_start = clock();
        if (verify(sig, clas.getPID(), clas.getpk(), clas.getU(), clas.getPub(), msg, clas.getTimestamp())) {
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
    vector<ECn> vecPK;
    vector<long> vecT;
    stringstream sth3,sth4;
    Big h3,h4;
    ECn temp, aggSig;
    for (int i = 0; i < n; i++) {
        ourclas.reg();
        Big sig = ourclas.sign(msg);
        sth3 << ourclas.getPID().AID << ourclas.getPID().T << ourclas.getpk() << ourclas.getU() << msg << ourclas.getTimestamp();
        Big h3 = Hash(sth3);
        temp = sig * g;
        temp -= ourclas.getU();
        temp *= inverse(h3,q);

        sth4 << temp;

        aggSig += temp;
        vecU.push_back(ourclas.getU());
        vecPID.push_back(ourclas.getPID());
        vecPK.push_back(ourclas.getpk());
        vecT.push_back(ourclas.getTimestamp());
    }
    h4 = Hash(sth4);
    double start = clock();
    if (aggVerify(n, msg, aggSig, h4, vecPID, vecPK, vecU, vecT)) {
        double end = clock();
        printf("[*] %d Aggregate Verification Time: %.6fms\n", n, (end - start) / CLOCKS_PER_SEC * 1000.0);
    }
}

int main() {
    irand(2022l); // 置随机种子
    setup();
    cout << endl << "------------Our-------------" << endl;
    OurCLAS ourclas;
    //singleTest(ourclas);
    avgTest(ourclas, 1000);
    aggTest(ourclas, 100);
    aggTest(ourclas, 200);
    aggTest(ourclas, 300);
    aggTest(ourclas, 400);
    aggTest(ourclas, 500);
    return 0;
}