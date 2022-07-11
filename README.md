
## Direct Deployent 

### Specifications

- OS: Linux x64, MAC OS x64

- Language: C++

- Requires: OpenSSL

- The default elliptic curve is "NID_secp256k1"


### Installation

The current implementation is based on OpenSSL library. See the installment instructions of OpenSSL as below:  

1. Clone the code [openssl-master](https://github.com/openssl/openssl.git)

```
    git clone https://github.com/openssl/openssl.git
```

2. install openssl on your machine

```
    ./config --prefix=/usr/local/ssl shared
    make 
    sudo make install
    export OPENSSL_ROOT_DIR=/usr/local/ssl/
```


### Testing


To compile and test the system, do the following: 

```
  $ cd {PATH}/ZKP_PHE_1bit
  $ mkdir build && cd build
  $ cmake ..
  $ make
  $ ./test_zkp_phe_1bit
```



