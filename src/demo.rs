extern crate bellman;
extern crate sapling_crypto;
extern crate crypto;
extern crate rand;

use bellman::pairing::ff::{
    PrimeField,
    PrimeFieldRepr,
    Field,
    BitIterator
};

use bellman::pairing::{
    Engine
};

use bellman::{
    SynthesisError,
    ConstraintSystem,
    Circuit
};

use sapling_crypto::circuit::{
    Assignment,
    boolean,
    ecc,
    sha256,
    num,
    multipack,
};

use sapling_crypto::jubjub::{
    JubjubEngine,
    FixedGenerators,
    PrimeOrder,
    Unknown,
    edwards,
    JubjubParams
};

// size for witnesses
const NUM_VALUE_BITS: usize = 128;
const NUM_BLINDING_BITS: usize = 128;


//1.you have to prove that you know these values inside your account
// by supplying it to an external entity
//every operation inside the snark in some finite field in our case in some prime order
//infromation about my current state
//to get your current account state you have to hash blinding bits and
 //values bits and conccatanate them together and hash them (similar to merkle tree)
//this is much cleaner to define every witness as an optional
//cause the cuircuit must not depend on the witness
//if blinded bits represent a empty vector, out curcuit should work...
#[derive(Clone)]
pub struct AccountWitness {
    pub old_blinding_bits: Vec<Option<bool>>,
    pub new_blinding_bits: Vec<Option<bool>>,
    pub value_bits: Vec<Option<bool>>,
}

//  we make a a snark on accountwitnes and 
// we decrease the balance of accountwitness and supply the information to external entity
//this is pedersen commitment with the value and blinding
//inside finite field you can create another eliptic curve 
//which in twisted edwards form for effiecincy of computation
#[derive(Clone)]
pub struct UTXOWitness<E: JubjubEngine> {
    pub value: Option<E::Fr>,
    pub blinding: Option<E::Fr>,
    // pub commitment: Option<edwards::Point<E, PrimeOrder>>
}
//encodes my balance and some blindning
//this will be a circuit 
//jubjub engine for zk snarks for which embeddec jabjab curve is defined
//Params is a trait that defiens these parameters
//you can generate Params using your gadget library
pub struct ConfidentialAccount<'a, E: JubjubEngine> {
    pub params: &'a E::Params,

    // supply the current account state
    //it wil be our public input
    //you will prove that you do propoer manipulanious on it
    //Fr is scalar field inside the main group
    pub current_state: Option<E::Fr>,

    // Witnesses
    pub witness: AccountWitness,

    // UTXO witness
    pub utxo: UTXOWitness<E>
}
//it used for clone the curcuit
impl<'a, E:JubjubEngine + 'a> Clone for ConfidentialAccount<'a, E> {
    fn clone(&self) -> Self {
        ConfidentialAccount {
            params: self.params,
            current_state: self.current_state.clone(),
            witness: self.witness.clone(),
            utxo: self.utxo.clone()
        }
    }
}

//implementation of circuit trait
//syntesize circuit in some constraint system
impl<'a, E: JubjubEngine> Circuit<E> for ConfidentialAccount<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError>
    {
        assert_eq!(self.witness.old_blinding_bits.len(), NUM_BLINDING_BITS);
        assert_eq!(self.witness.new_blinding_bits.len(), NUM_BLINDING_BITS);
        assert_eq!(self.witness.value_bits.len(), NUM_VALUE_BITS);

        // Expose the current truncated hash as the input
        //represent current account state
        //name space has two parameters defined as closures
        //as soon we generate these parameters we never rely on witness
        //current_state is our public input
        let current = num::AllocatedNum::alloc(
            cs.namespace(|| "current account state"),
            // this part is never evaluated, so you can not depend on it in your curcuit
            //in case of failure it will return SynthesisError
            || {
                let value = self.current_state;
                Ok(*value.get()?)
            }
        )?;
         //make another variable constrainted
         //if something happdns you know where it is happned
         //current is a public input
        current.inputize(cs.namespace(|| "current state input"))?;

        //blindings bits and values are private variables

        let mut blinding_bits = Vec::<boolean::Boolean>::with_capacity(NUM_BLINDING_BITS);
        // allocate bits for use of sha256 
        // allocatedBit is just a variable which is internally contrained be either 0 or 1
        for i in 0..NUM_BLINDING_BITS {
            //Boolean is a wrapper , it reduces the number of contraints in your circuit
           //if you compute AND for two booleans ( that are true ) ,it outputs true
            let bit = boolean::Boolean::from(
                boolean::AllocatedBit::alloc(
                    // first par format is a macro which will allow us to make a string
                    //if something happns we know where it happens
                    //secpdn parameter is an option
                    cs.namespace(|| format!("allocating blinding bit {}", i)),
                    self.witness.old_blinding_bits[i]
                )?
            );
            blinding_bits.push(bit);
        }

        let mut value_bits = Vec::<boolean::Boolean>::with_capacity(NUM_VALUE_BITS);

        for i in 0..NUM_VALUE_BITS {
            let bit = boolean::Boolean::from(boolean::AllocatedBit::alloc(
                cs.namespace(|| format!("allocating value bit {}", i)),
                self.witness.value_bits[i]
                )?
            );
            value_bits.push(bit);
        }

        // use bit in to calculate a value

        // make a linear combination from bit decomposition
        //linear combination is an expression constructed from a set of terms by multiplying each term by a constant and adding the results 
        //bit[0 in littleendian]coef[0](1)+ coef[1[(doudled)*bit[1]+...etc
        let mut coeff = E::Fr::one();
        let mut num_lc = num::Num::<E>::zero();
        for bit in value_bits.iter() {
            //multiplication of a bit and coffictient
            num_lc = num_lc.add_bool_with_coeff(CS::one(), bit, coeff);
            coeff.double();//2,4, 8 etc
        }
        //make a variable for num_lc 
        //? why we can not just declare num_rc before  "for bit in value_bits.iter()""
        // allocate some number that should be equal to this combination
        let value = num::AllocatedNum::alloc(
            cs.namespace(|| "current value"), 
            || {
                let value = num_lc.get_value();

                Ok(*value.get()?)
            }
        )?;

        // enforce!
           // something like a / b == c
           //we enforce that value variable is equal to our linear combination
        cs.enforce(
            || "enforce current value allocation",
            |lc| lc + value.get_variable(),
            |lc| lc + CS::one(),
            // `lc` function returns `lc` scaled by the specified constant. In our case the constant is one
            |_| num_lc.lc(E::Fr::one()) 
        );

        // calculate the hash value

        // merge vectors
         //merge 128 blinding_bits and 128 value_bits

         //there are no bytes in a circuit, you always work with bits
        blinding_bits.extend(value_bits);
        //? why we cs.namespace inside sha256?
        //hash is the set of bits
        let mut hash = sha256::sha256(
            cs.namespace(|| "calculate old state hash"),
            &blinding_bits
        )?;

        //big endian means that most significant bit is first 

        //we have to tie this hash with value from line 130 public variable

        // hash is now is just an array of 256 bits. Our field is limited
        // in number of bits that input can represent, so we need to truncate some of the bits

        // for convenience we reverse the array, trucrate it and interpret the rest as LE decomposition
        // of the field element

         
        // it is similar if i take a solidity fucntion and cast it to unsigned integer of 256 bits
        hash.reverse();//we have the least significant bit first
        //there is no guarantee that every 255 bit number can be represented within the size of this field
         //this is basically is bit length of the field modulus minus 1
        hash.truncate(E::Fr::CAPACITY as usize);//we dont take a highest bitcause our capacity is limited

        //we do linear combination
        let mut packed_hash_lc = num::Num::<E>::zero();
        let mut coeff = E::Fr::one();
        for bit in hash {
            packed_hash_lc = packed_hash_lc.add_bool_with_coeff(CS::one(), &bit, coeff);
            coeff.double();
        }
         //enforce linear combination to be equal current public vairiable from line 130
         //this is a way how to tie something from circuit(hash of private inputs : value_bits and blindings_bits
         //) with public input(e.g solidity contract)
        cs.enforce(
            || "enforce state equality to external input",
            |lc| lc + current.get_variable(),
            |lc| lc + CS::one(),
            |_| packed_hash_lc.lc(E::Fr::one())
        );

        // if time permits we can now also make an UTXO design

        let utxo_value = num::AllocatedNum::alloc(
            cs.namespace(|| "utxo value"),
            || {
                let value = self.utxo.value;
                Ok(*value.get()?)
            }
        )?;

        utxo_value.limit_number_of_bits(
            cs.namespace(|| "limit number of bits for value"),
            NUM_VALUE_BITS
        )?;
        //decompose the value into the bits with little endina
        let utxo_bits = utxo_value.into_bits_le(
            cs.namespace(|| "get utxo value bits")
        )?;
        //? what means this construction
        let utxo_blinding = num::AllocatedNum::alloc(
            cs.namespace(|| "utxo blinding"),
            || {
                let value = self.utxo.blinding;
                Ok(*value.get()?)
            }
        )?;

        let blinding_bits = utxo_blinding.into_bits_le(
            cs.namespace(|| "get blinding bits")
        )?;

         // we work with pedersen commitment that will be exposed to our external servers
         //fixed based multiplication
         //there isa generator for a curve that is fixed
         // you just mutliple this point by scalar
        let value_point = ecc::fixed_base_multiplication(
            cs.namespace(|| "value * G"), 
            FixedGenerators::ValueCommitmentValue, 
            &utxo_bits, 
            self.params
        )?;

        let blinding_point = ecc::fixed_base_multiplication(
            cs.namespace(|| "blinding * H"), 
            FixedGenerators::ValueCommitmentRandomness, 
            &blinding_bits, 
            self.params
        )?;
           //value_points adds blinding_factor
        let commitment_point = value_point.add(
            cs.namespace(|| "calculate commitment"),
            &blinding_point, 
            self.params
        )?;
         //make commitmentpoint public
         //(x, y) points are a part of our public input
        commitment_point.inputize(
            cs.namespace(|| "make commitment as input")
        )?;
        

        //we have properly reduce the balance
        //this is a way of how we calculate the witness
        let remaining_value = num::AllocatedNum::alloc(
            cs.namespace(|| "remaining value"), 
            || {
                let mut v1 = *value.get_value().get()?;
                let v2 = *utxo_value.get_value().get()?;

                v1.sub_assign(&v2);

                Ok(v1)  //we return a result
            }
        )?;
         // remaminng_value is multiplied by one in a form A * B = C
         //why u use lc here?
        cs.enforce(
            || "enforce value reduction",
            |lc| lc + remaining_value.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + value.get_variable() - utxo_value.get_variable()
        );
    
         //prevent overflow
        remaining_value.limit_number_of_bits(
            cs.namespace(|| "limit number of bits in remaining value"),
            NUM_VALUE_BITS
        )?;

        Ok(())
    }
}