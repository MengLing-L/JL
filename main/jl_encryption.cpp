#define DEBUG
#define BHJL_HE_MR_INTERATIONS 16

#include "gen_prime.cpp"
#include <map>
#include <math.h>
#include <iostream>
using namespace std;
const unsigned long int Y_P_LEN = 1025;
const unsigned long int MAX_IT_LEN = 170;
map<unsigned long int, mpz_t> y_p_map;
map<unsigned long int, map<unsigned long int,mpz_t>> IT;

void ypmap_new(map<unsigned long int, mpz_t> &map, unsigned long int k)
{
    for(unsigned long int i = 1; i < k + 1; i++){
        mpz_init (map[i]);
    }
}

void itmap_new(map<unsigned long int, map<unsigned long int, mpz_t>> &map)
{
    for(unsigned long int i = 1; i < MAX_IT_LEN; i++){
        for(unsigned long int j = 1; j < Y_P_LEN; j++){
		mpz_init (map[i][j]);
	}
    }
}

void ypmap_clear(std::map<unsigned long int, mpz_t> &map, unsigned long int k)
{
    for(unsigned long int i = 1; i < k + 1; i++){
        mpz_clear (map[i]);
    }
}

void itmap_clear(map<unsigned long int, map<unsigned long int, mpz_t>> &map)
{
    for(unsigned long int i = 1; i < MAX_IT_LEN; i++){
        for(unsigned long int j = 1; j < Y_P_LEN; j++){
		mpz_clear (map[i][j]);
	}
    }
}

struct JL_PK
{
    mpz_t N;
    mpz_t y;
    mpz_t h;
    unsigned long int k;
    mpz_t x;
};

struct JL_SK
{
    mpz_t p;
    mpz_t alpha;
};

struct JL_Ciphertext{
    mpz_t c;
};

JL_PK * JL_PK_new()
{ 
    JL_PK *jl_pk;
    jl_pk = (JL_PK *)malloc(sizeof(*jl_pk));
    mpz_init(jl_pk->N);
    mpz_init(jl_pk->y);
    mpz_init(jl_pk->h);
    mpz_init(jl_pk->x);
    return jl_pk;
}

void JL_PK_free(JL_PK* jl_pk)
{ 
    mpz_clear(jl_pk->N);
    mpz_clear(jl_pk->y);
    mpz_clear(jl_pk->h);
}

JL_SK * JL_SK_new()
{ 
    JL_SK *jl_sk;
    jl_sk = (JL_SK *)malloc(sizeof(*jl_sk));
    mpz_init(jl_sk->p);
    mpz_init(jl_sk->alpha);
    ypmap_new(y_p_map, Y_P_LEN);
    itmap_new(IT);
    return jl_sk;
}

void JL_SK_free(JL_SK* jl_sk)
{ 
    mpz_clear(jl_sk->p);
    mpz_clear(jl_sk->alpha);
    ypmap_clear(y_p_map, Y_P_LEN);
    itmap_clear(IT);
}


JL_Ciphertext *JL_Ciphertext_new()
{ 
    JL_Ciphertext * jl_ciphertext;
    jl_ciphertext = (JL_Ciphertext *)malloc(sizeof(*jl_ciphertext));
    mpz_init(jl_ciphertext->c);
    return jl_ciphertext;
}

void JL_Ciphertext_free(JL_Ciphertext* jl_ciphertext)
{ 
    mpz_clear(jl_ciphertext->c);
}

/*
fn two_over(n: &BigInt) -> i8 {
    if n.mod_floor(&BigInt::from(8)) == BigInt::one()
        || n.mod_floor(&BigInt::from(8)) == BigInt::from(7)
    {
        1
    } else {
        -1
    }
}*/
int8_t two_over(mpz_srcptr n){
    mpz_t tmp_r;
    mpz_init(tmp_r);
    mpz_fdiv_r_ui(tmp_r, n, 8);

    if(mpz_cmp_ui(tmp_r, 1) == 0 || mpz_cmp_ui(tmp_r, 7) == 0){
        mpz_clear(tmp_r);
        return 1;
    }else{
        mpz_clear(tmp_r);
        return -1;
    }
}

/*fn reciprocity(num: &BigInt, den: &BigInt) -> i8 {
    if num.mod_floor(&BigInt::from(4)) == BigInt::from(3)
        && den.mod_floor(&BigInt::from(4)) == BigInt::from(3)
    {
        -1
    } else {
        1
    }
}*/
int8_t reciprocity(mpz_srcptr num, mpz_srcptr den){
    mpz_t tmp_r, tmp_r1;
    mpz_init(tmp_r);
    mpz_init(tmp_r1);
    mpz_fdiv_r_ui(tmp_r, num, 4);
    mpz_fdiv_r_ui(tmp_r1, den, 4);
    if (mpz_cmp_ui(tmp_r, 3) == 0 && mpz_cmp_ui(tmp_r1, 3) == 0){
        mpz_clear(tmp_r);
        mpz_clear(tmp_r1);
        return -1;
    }else{
        mpz_clear(tmp_r1);
        mpz_clear(tmp_r);
        return 1;
    }
}

void compute_nth_power_residue_symbol(mpz_ptr nth_power_res, mpz_srcptr a, mpz_srcptr p, mpz_srcptr N){
	mpz_t ONE;
	mpz_init (ONE);

	mpz_set_ui (ONE, 1);
	mpz_sub(nth_power_res, p, ONE); // p - 1
	mpz_fdiv_q (nth_power_res, nth_power_res, N);// (p-1)/N
	mpz_powm (nth_power_res, a, nth_power_res, p);// a^((p-1)/N)) mod p

	mpz_clear (ONE);
}

int8_t jacobi(mpz_srcptr a, mpz_srcptr n){
    mpz_t tmp_r, TWO, num, den;
    mpz_init(tmp_r);
    mpz_init(TWO);
    mpz_init(num);  
    mpz_init(den); 
    //if n.mod_floor(&BigInt::from(2)) == zero || n <= &BigInt::zero() {
    //    return None;
    //}
    mpz_set_ui (TWO, 2);
    mpz_fdiv_r(tmp_r, n, TWO);

    if(mpz_cmp_ui(tmp_r, 0) == 0 || mpz_cmp_ui(n, 0) <= 0){
        mpz_clear(tmp_r);
        mpz_clear(TWO);
        mpz_clear(num);
        mpz_clear(den);
        return NULL;
    }

    //let mut acc = 1;
    //let mut num = a.mod_floor(&n);
    //let mut den = n.clone();
    int8_t acc = 1;
    mpz_fdiv_r(num, a, n);
    mpz_set (den, n);

    while(true){
        //num = num.mod_floor(&den);
        //if num == zero {
        //    return Some(0);
        //}
        mpz_fdiv_r(num, num, den);
        if(mpz_cmp_ui(num, 0) == 0) {
            mpz_clear(tmp_r);
            mpz_clear(TWO);
            mpz_clear(num);
            mpz_clear(den);
            return 0;
        }

        //while num.mod_floor(&BigInt::from(2)) == zero {
        //    acc *= two_over(&den);
        //    num = num.div_floor(&BigInt::from(2));
        //}
        mpz_fdiv_r_ui(tmp_r, num, 2);
        while (mpz_cmp_ui(tmp_r, 0) == 0){
            acc *= two_over(den);
            mpz_fdiv_q(num, num, TWO);
            mpz_fdiv_r_ui(tmp_r, num, 2);
        }
        //if num == BigInt::one() {
        //    return Some(acc);
        //}
        // shared factors => one sub-symbol is zero
        //if num.gcd(&den) > BigInt::one() {
        //    return Some(0);
        //}
        if(mpz_cmp_ui(num, 1) == 0){
            mpz_clear(tmp_r);
            mpz_clear(TWO);
            mpz_clear(num);
            mpz_clear(den);
            return acc;
        }
        mpz_gcd(tmp_r, num, den);
        if(mpz_cmp_ui(tmp_r, 1) > 0){
            mpz_clear(tmp_r);
            mpz_clear(TWO);
            mpz_clear(num);
            mpz_clear(den);
            return 0;
        }
        //acc *= reciprocity(&num, &den);
        //let tmp = num;
        //num = den.clone();
        //den = tmp;
        acc *= reciprocity(num, den);
        mpz_set (tmp_r, num);
        mpz_set (num, den);
        mpz_set (den, tmp_r);
    }
    
}
/*pub fn choose_non_quadratic_residual(p: &BigInt, q: &BigInt, N: &BigInt) -> BigInt {
    let mut x = BigInt::sample_below(&N);
    loop {
        if jacobi(&x, &p).unwrap() == -1 && jacobi(&x, &q).unwrap() == -1 {
            break;
        }
        else {
            x = BigInt::sample_below(&N);
        }
    }
    x
}*/

void choose_non_quadratic_residual(mpz_ptr x, mpz_srcptr p, mpz_srcptr q, mpz_srcptr N, unsigned long int tmp_seed){
    mpz_t seed;
    gmp_randstate_t prng;
    gmp_randinit_mt(prng);

    mpz_init(seed);
    mpz_set_ui(seed, tmp_seed);
    gmp_randseed(prng, seed);

    size_t bits = mpz_sizeinbase(N, 2);
    while(true){
        while(true){
            mpz_urandomb(x, prng, bits);
            if (mpz_cmp(x, N) < 0) {
                break;
            }
        }
        if (jacobi(x, p) == -1 && jacobi(x, q) == -1) {
            break;
        }
    }

    mpz_clear (seed);
    gmp_randclear (prng);

}


void JL_KeyGen(unsigned long int k,JL_PK *pk,  JL_SK *sk, unsigned long int p_bits, unsigned long int q_bits, unsigned long int tmp_seed){
    pk->k = k;
    unsigned long int l = 10, s = (unsigned long int)(pk->k/l);
    mpz_t seed,tmp_r,two_pow_k,q,two_pow_l,y_p_2l,two_pow_i;
    
    mpz_init(y_p_2l);
    mpz_init(tmp_r);
    mpz_init(two_pow_i);
    mpz_init(two_pow_l);
    mpz_init(two_pow_k);
    mpz_init(q);
    mpz_init(seed);
    gmp_randstate_t prng;
    gmp_randinit_mt(prng);
    mpz_set_ui(seed, tmp_seed);
    gmp_randseed(prng, seed);

    //compute 2 pow k
    mpz_ui_pow_ui(two_pow_k, 2, pk->k);

    //generate p
    generate_prime_optimized(sk->p, p_bits, p_bits - 1, pk->k, tmp_seed);

    //generate q
    generate_prime_optimized(q, q_bits, q_bits - 1, 1, tmp_seed);

    //compute N=pq
    mpz_mul(pk->N, sk->p, q);

    choose_non_quadratic_residual(pk->x, sk->p, q, pk->N, tmp_seed);

    size_t bits = mpz_sizeinbase(pk->N, 2);
    while(true){
        mpz_urandomb(sk->alpha, prng, bits);
        if (mpz_cmp(sk->alpha, pk->N) < 0) {
            break;
        }
    }
    // ensure alpha is odd
    mpz_fdiv_r_ui(tmp_r, sk->alpha, 2);
    if (mpz_cmp_ui(tmp_r, 0) == 0){
        mpz_sub_ui(sk->alpha, sk->alpha, 1);
    }

    mpz_powm(pk->y, pk->x, sk->alpha, pk->N);
    mpz_powm(pk->h, pk->x, two_pow_k, pk->N);

    mpz_ui_pow_ui (two_pow_l, 2, l);
    compute_nth_power_residue_symbol(y_p_2l, pk->y, sk->p, two_pow_l);

    mpz_set_ui (y_p_map[0], 1);
    for(unsigned long int i = 1; i < (unsigned long int)pow(2,l); i++){
    	mpz_powm_ui (y_p_map[i], y_p_2l, i, sk->p);
    }

    for(unsigned long int i = 1; i < s + 1; i++){
	    mpz_ui_pow_ui (two_pow_i, 2, i*l);
	    compute_nth_power_residue_symbol(y_p_2l, pk->y, sk->p, two_pow_i);
        for(unsigned long int j = 1; j < (unsigned long int)pow(2,l); j++){
            mpz_powm_ui (IT[i][j], y_p_2l, j, sk->p);
            mpz_invert (IT[i][j], IT[i][j], sk->p);
	    }
    }

    mpz_clear (two_pow_i);
    mpz_clear (y_p_2l);
    mpz_clear (tmp_r);
    mpz_clear (two_pow_l);
    mpz_clear (two_pow_k);
    mpz_clear (q);
    mpz_clear (seed);
    gmp_randclear (prng);
}


void JL_Encrypt(mpz_srcptr m, mpz_srcptr r, JL_Ciphertext *jl_ciphertext, JL_PK *pk){
    mpz_t c1,c2;
    mpz_init(c1);
    mpz_init(c2);

    mpz_powm(c1, pk->y, m, pk->N);
    mpz_powm(c2, pk->h, r, pk->N);

    mpz_mul(jl_ciphertext->c, c1, c2);
    mpz_fdiv_r(jl_ciphertext->c, jl_ciphertext->c, pk->N);

    mpz_clear(c1);
    mpz_clear(c2);
}

void JL_decrypt(mpz_ptr recover_m, JL_Ciphertext *jl_ciphertext, JL_PK *pk, JL_SK *sk){
    unsigned long int l = 10, s = (unsigned long int)(pk->k/l);
    mpz_t two_pow_k,TWO,t,tmp_m,r;
	mpz_init (two_pow_k);
	mpz_init (TWO);
	mpz_init (t);
	mpz_init (tmp_m);
	mpz_init (r);
	
	mpz_set_ui (TWO, 2);
	mpz_pow_ui (two_pow_k, TWO, s*l);
    map<unsigned long int, mpz_t> Z_map;
    ypmap_new(Z_map, s);

	compute_nth_power_residue_symbol(Z_map[s], jl_ciphertext->c, sk->p, two_pow_k);

	for(size_t z_index = s - 1; z_index > 0; z_index--){
		mpz_powm_ui (Z_map[z_index], Z_map[z_index + 1], (unsigned long int) pow(2, l), sk->p);// z[i+1]^2 mod p
	}
	
    for(unsigned long int i = 1; i < s + 1; i++){
		unsigned long int itindex;
		mpz_set (tmp_m, recover_m);
		mpz_set (t, Z_map[i]);
		
		size_t shift = 1;
		size_t m_size = mpz_sizeinbase(tmp_m, 2);
		while(mpz_cmp_ui (tmp_m, 0) > 0 && shift < i){
			itindex = mpz_fdiv_r_ui (r, tmp_m, (unsigned long int) pow(2, l));
			if (itindex != 0){
				mpz_mul (t, t, IT[i - shift + 1][itindex]);
				mpz_mod (t, t, sk->p);
			}
			shift = shift + 1;
			mpz_fdiv_q_2exp(tmp_m, tmp_m, l);
		}
		for (std::map<unsigned long int, mpz_t>::iterator it=y_p_map.begin(); it!=y_p_map.end(); ++it){
			if (mpz_cmp(t, it->second) == 0){
				mpz_set_ui (tmp_m, it->first);
				mpz_mul_2exp (tmp_m, tmp_m, (i - 1)*l);
				mpz_add (recover_m, recover_m, tmp_m);
			}
		}
	}
	
	mpz_clear (two_pow_k);
	mpz_clear (TWO);
	mpz_clear (t);
	mpz_clear (tmp_m);
}


int main()
{
    mpz_t m,recover_m,r;
    mpz_init(m);
    mpz_init(r);
    mpz_init(recover_m);
    mpz_t seed;
    gmp_randstate_t prng;
    gmp_randinit_mt(prng);
    
    
    JL_PK *jl_pk = JL_PK_new();
    JL_SK *jl_sk = JL_SK_new();
    JL_Ciphertext *jl_ciphertext = JL_Ciphertext_new();
    

    unsigned long int k = 910;
    unsigned long int p_bits=2080, q_bits=2080;
    //unsigned long int k = 1160;
    //unsigned long int p_bits=3840, q_bits=3840;
    cout << "k bits: " << k << ", p bits: " << p_bits << endl; 

    auto start_time = chrono::steady_clock::now();
    JL_KeyGen(k, jl_pk, jl_sk, p_bits, q_bits, 23423);
    auto end_time = chrono::steady_clock::now(); // end to count the time
    auto running_time = end_time - start_time;
    cout << "Key generation takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;
    mpz_init(seed);
    mpz_set_ui(seed, 234234);
    gmp_randseed(prng, seed);
    mpz_urandomb(r, prng, k-20);
    mpz_urandomb(m, prng, k-2);
    //mpz_set_ui(m, 234234);

    gmp_printf ("m: %Zd\n", m);
    start_time = chrono::steady_clock::now();
    JL_Encrypt(m, r, jl_ciphertext, jl_pk);
    end_time = chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    cout << "Encryption takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;
    mpz_set_ui (recover_m, 0);

    start_time = chrono::steady_clock::now();
    JL_decrypt(recover_m, jl_ciphertext, jl_pk, jl_sk);
    gmp_printf ("recover_m: %Zd\n", recover_m);
    end_time = chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    cout << "Decryption takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;


    k = 1160;
    p_bits=3840, q_bits=3840;
    cout << "k bits: " << k << ", p bits: " << p_bits << endl;
    start_time = chrono::steady_clock::now();
    JL_KeyGen(k, jl_pk, jl_sk, p_bits, q_bits, 23423);
    end_time = chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    cout << "Key generation takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;
    mpz_init(seed);
    mpz_set_ui(seed, 234234);
    gmp_randseed(prng, seed);
    mpz_urandomb(r, prng, k-20);
    mpz_urandomb(m, prng, k);
    //mpz_set_ui(m, 234234);

    gmp_printf ("m: %Zd\n", m);
    start_time = chrono::steady_clock::now();
    JL_Encrypt(m, r, jl_ciphertext, jl_pk);
    end_time = chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    cout << "Encryption takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;
    mpz_set_ui (recover_m, 0);

    start_time = chrono::steady_clock::now();
    JL_decrypt(recover_m, jl_ciphertext, jl_pk, jl_sk);
    gmp_printf ("recover_m: %Zd\n", recover_m);
    end_time = chrono::steady_clock::now(); // end to count the time
    running_time = end_time - start_time;
    cout << "Decryption takes time = "
    << chrono::duration <double, milli> (running_time).count() << " ms" << endl;


    mpz_clear (seed);
    gmp_randclear (prng);
    JL_SK_free(jl_sk);
    JL_PK_free(jl_pk);
    JL_Ciphertext_free(jl_ciphertext);
    mpz_clear(m);
    mpz_clear(recover_m);
    return 0;
}





