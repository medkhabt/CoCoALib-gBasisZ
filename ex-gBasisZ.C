// Copyright (c) 2006  John Abbott,  Anna M. Bigatti
// This file is part of the CoCoALib suite of examples.
// You are free to use any part of this example in your own programs.

#include "CoCoA/library.H"

using namespace std;

//----------------------------------------------------------------------
const string ShortDescription =
"Contains functions that compute strong Gröbner bases over the integers \n";
  

const string LongDescription =
  "Make a copy of this file (called \"foo.C\", say) and put your code \n"
  "inside the procedure \"program\".                                  \n"
  "To compile your file in the examples directory just do this:       \n"
  "  make foo                                                         \n";
//----------------------------------------------------------------------
// i need more examples for bigger polynomials, or for polynomials that will give a result of non one.

class UselessSpecialPoly: public exception {
    const string m_msg;
    public:
    UselessSpecialPoly(const string& msg): m_msg(msg) {
//        cout << "NoElementFoundException::NoElementFoundException - set m_msg to: " << m_msg << endl;
    }
    
    
};
namespace CoCoA
{
    
    
    RingElem gcdPolynomial(ConstRefRingElem a, ConstRefRingElem b);
    RingElem sPolynomial(ConstRefRingElem a, ConstRefRingElem b);
    bool isSPolyUseless(ConstRefRingElem f, ConstRefRingElem g);
    bool isGcdPolyUseless(ConstRefRingElem f, ConstRefRingElem g);
    //TODO:
    // better name, sugg: RemQuots.
    class RemQuots {
        private: // data members;
            RingElem remainder;
            std::vector<RingElem> quotients;
        public :
            RemQuots(ConstRefRingElem, const std::vector<RingElem>&);
            explicit RemQuots(ConstRefRingElem);
            const RingElem& getRemainder() const{
                return this->remainder;
            }
            const std::vector<RingElem>& getQuotients() const{
                return this->quotients;
            }
        
        
    };
    
    // call a constructor to the other construcotr.
    // we explicitly allow an empty vector. maybe not do that in thefuture
    // TODO: we should check that all the elements in the vector should be in the same ring of r.
    RemQuots::RemQuots(ConstRefRingElem r, const std::vector<RingElem>& q) : remainder(r), quotients(q){}

    RemQuots::RemQuots(ConstRefRingElem r) :remainder(r){}
    
    //TODO: in the choose method, when the flags for gcd and s are down remove the object from the array
    class SpecialPolysController {
        private:
            RingElem f;
            RingElem g;
            bool usedGcd, usedS;
        public:
        SpecialPolysController(const RingElem f1, const RingElem f2);
        // TODO: Check if it is used anymore.
        bool equals(SpecialPolysController obj) const{
            return usedGcd == obj.getUsedGcd() && usedS == obj.getUsedS() && f == obj.getF() && g == obj.getG();
        }
        const RingElem& getF() {
            return f;
        }
        const RingElem& getG() {
            return g;
        }
        bool getUsedGcd() {
            return usedGcd;
        }
        bool getUsedS() {
            return usedS;
        }
        
        // return type is bool if there is something to return it says true, if both of the gcd and s are already used it means there is nothing to choose.
        bool isUsed() {
            return usedGcd && usedS;
        }
        RingElem choose() {
//            std::cout << "inside the choose method" << endl;
//            cout << "initial values: usedGcd: " << usedGcd << ", usedS: " << usedS << endl;
            
//            cout << "after useless check: usedGcd: " << usedGcd << ", usedS: " << usedS << endl;
            std::ostringstream oss;
            oss << "this object is already used! f: " << f << ", g: " << g;
            if(usedS && usedGcd) throw std::invalid_argument(oss.str()); // TODO: Throw an exception.
            if(isSPolyUseless(f,g)) {
                usedS = true;
            }
            
            if(isGcdPolyUseless(f,g)) {
                usedGcd = true;
            }
            if(usedS && usedGcd) throw UselessSpecialPoly("gcd and s poly are reduced to zero.");
            RingElem resultGcd = gcd();
            // TODO: break the cond. to !usedS than if(!usedGcd) -> calcu. rgcd than the other part of the cond.
            if( !usedS && ( usedGcd || (IsDivisible( LC(this -> f), LC(resultGcd) ) && IsDivisible( LC(this -> g), LC(resultGcd)))  )  ) {
                usedS = true;
//                usedGcd = true;
//                if( IsZero(s()) && !usedGcd) { // TODO: i don't know why at one point the usedS doesn't want to update to true, maybe i create a new instance each time
//                    // anyways i added this to counter that for now.
//                    usedGcd = true;
//                    return resultGcd;
//                }
              
//                cout << "we used s usedGcd: " << usedGcd << ", usedS: " << usedS << endl;
//                cout << "result of s is : " << s() << endl;
//                cout << "functions are: f: " << f << ", g: " << g << endl;
                return s();
            }
            usedGcd = true;
//            usedS= true;
//            cout << "we used gcd usedGcd: " << usedGcd << ", usedS: " << usedS << endl;
//            cout << "result of gcd is : " << resultGcd << endl;
            return resultGcd;
//            else {
//                return gcd();
//            }
        }
        const RingElem gcd() const{
            return gcdPolynomial(this->f,this->g);
        }
        const RingElem s() const{
            return sPolynomial(this->f, this->g);
        }
        
    };
    // TODO: check if they are from the same ring.
    SpecialPolysController::SpecialPolysController(const RingElem f1, const RingElem f2) : f(f1), g(f2) {
        usedS = false;
        usedGcd = false;
    }
    
    RingElem topReduction(const BigInt& aCoef,ConstRefRingElem h, ConstRefRingElem g) {
        RingElem aAndLmQuotient = monomial(owner(h), aCoef, LPP(h)/LPP(g));
        return h - aAndLmQuotient * g;
    }
    
    RingElem NF(RingElem f, const std::vector<RingElem>& generators) {
            while(!IsZero(f)) {
                CheckForInterrupt("interrupt NF");
                BigInt a;
                RingElem g;
                
                auto isElementTopReduces =
                    [&f, &a](ConstRefRingElem& element){
                        BigInt LCofF = ConvertTo<BigInt>(LC(f));
                        BigInt LCofElem = ConvertTo<BigInt>(LC(element));
                        // if ( LCofElm > LCofH ) -> false (both cond of !isZero and the reminder of lcofh / lcofelem is smaller than lcofF)
                        if(!IsDivisible(LPP(f), LPP(element)))
                            return false;
                        if(abs(LCofElem) > abs(LCofF))
                            return false;
                        a = LCofF / LCofElem;
                        return true;
                };

                const auto result = std::find_if(begin(generators), end(generators), isElementTopReduces);
                
                if(result == std::end(generators)) {
                    return f;
                }
                g = *result;
//                cout << "result inside Nf from f: " << f << " and g: " << g << "is: " << g << endl;
                f = topReduction(a, f, g);
//                cout << "result after topReduction " << f << endl;
            }
        return f;
    }
    
    
    bool isNecessaryGcdPair(ConstRefRingElem a, ConstRefRingElem b){
        return ( !(IsDivisible(LC(a), LC(b))) && !(IsDivisible(LC(b), LC(a))) );
    }
    
    RingElem sPolynomial(ConstRefRingElem a, ConstRefRingElem b){
            RingElem lmA = monomial(owner(a), LC(a), LPP(a));
            RingElem lmB = monomial(owner(b), LC(b), LPP(b));

            RingElem numerator =
                        lcm(lmA, lmB);
            return (numerator/lmA) * a - (numerator/lmB) * b;

        }
    
    RingElem sPolynomialNew(ConstRefRingElem a, ConstRefRingElem b){

        ConstRefPPMonoidElem lmA = LPP(a);
        ConstRefPPMonoidElem lmB = LPP(b);
        
        PPMonoidElem termLcm = lcm(lmA, lmB);
        
        
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));
        
        
        BigInt numerator = lcm(lcaValue, lcbValue);
        // af tf f - ag tg g //
        return monomial(owner(a), (numerator/lcbValue), (termLcm/lmA)) * a - monomial(owner(b), (numerator/lcaValue), (termLcm/lmB)) * b;

    }
    
    
    bool isGcdPolyUseless(ConstRefRingElem f,ConstRefRingElem g) {
        return (IsDivisible(LC(g), LC(f)));
    }
    
    bool isSPolyUseless(ConstRefRingElem f, ConstRefRingElem g){
        return (IsCoprime(LPP(f), LPP(g)) && IsCoprime(LC(f), LC(g)));
    }
    
    
    
//    bool isNecessarySPair(ConstRefRingElem a, ConstRefRingElem b) {
//        return ( gcd(
//                     monomial(owner(a), LC(a), LPP(a)),
//                     monomial(owner(b), LC(b), LPP(b))
//                     )
//                != 1);
//    }
//
    bool isNecessarySPair(ConstRefRingElem a, ConstRefRingElem b) {
        return ( !IsCoprime(LPP(a), LPP(b)) || !IsCoprime(LC(a), LC(b)) );
    }
    
    ConstRefPPMonoidElem LT(ConstRefRingElem a) {
//        RingElemAlias result = ;
        return LPP(a);
    }
    
    RingElem gcdPolynomial(ConstRefRingElem a, ConstRefRingElem b){
        ConstRefPPMonoidElem lta = LT(a);
        ConstRefPPMonoidElem ltb = LT(b);

        PPMonoidElem termLcm = lcm(lta, ltb);
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));

//        cout << "lcaValue " << lcaValue << ", lcbValue " << lcbValue << endl;
        GcdAndCofacs resultExt = ExtGcd(
                std::vector<BigInt>{lcaValue, lcbValue}); //GcdAndCofacs

//        cout << "cofacs are : " << resultExt.myCofacs.at(0) << ", " << resultExt.myCofacs.at(1) << endl;

//        if(IsOne(LPP(a))) {
//
//        }
//        else if(IsOne(LPP(b))) {
//
//        }
//        else {
//
//        }

//        RingElem result(owner(a), )
        //TODO:  in case one of the result have lpp equal to one.
        RingElem aPart = monomial(owner(a), resultExt.myCofacs.at(0), termLcm/lta);
//        cout << "aPart is one:" << IsOne(LPP(aPart)) << endl;
//        cout << "aPart lc " << LC(aPart) << " aPart LPP" << LPP(aPart) << endl;
        RingElem bPart = monomial(owner(b), resultExt.myCofacs.at(1), termLcm/ltb);
//        cout << "bPart is one:" << IsOne(bPart) << endl;
//        cout << "bPart lc " << LC(bPart) << " bPart LPP" << LPP(bPart) << endl;
//        cout << "the sum is zero" << IsZero(aPart + bPart) << endl;
        return (aPart * a + bPart * b); //
        //return ((D[1]*TermLcm)/LT(F))*F+((D[2]*TermLcm)/LT(G))*G
    }
    
    RingElem gcdPolynomialNew(ConstRefRingElem a, ConstRefRingElem b){
        // bf tf f + bg tg g // tf = t/ lmf tg = t/lmg // b = gcd lcf, lcg // gf
        ConstRefPPMonoidElem lma = LPP(a);
        ConstRefPPMonoidElem lmb = LPP(b);
        
        PPMonoidElem termLcm = lcm(lma, lmb);
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));
        
//        cout << "lcaValue " << lcaValue << ", lcbValue " << lcbValue << endl;
        GcdAndCofacs resultExt = ExtGcd(
                std::vector<BigInt>{lcaValue, lcbValue}); //GcdAndCofacs  this bf , bg ?
        
//        cout << "cofacs are : " << resultExt.myCofacs.at(0) << ", " << resultExt.myCofacs.at(1) << endl;
        
//        if(IsOne(LPP(a))) {
//
//        }
//        else if(IsOne(LPP(b))) {
//
//        }
//        else {
//
//        }
        
//        RingElem result(owner(a), )
        //TODO:  in case one of the result have lpp equal to one.
        RingElem aPart = monomial(owner(a), resultExt.myCofacs.at(0), termLcm/lma);
//        cout << "aPart is one:" << IsOne(LPP(aPart)) << endl;
//        cout << "aPart lc " << LC(aPart) << " aPart LPP" << LPP(aPart) << endl;
        RingElem bPart = monomial(owner(b), resultExt.myCofacs.at(1), termLcm/lmb);
//        cout << "bPart is one:" << IsOne(bPart) << endl;
//        cout << "bPart lc " << LC(bPart) << " bPart LPP" << LPP(bPart) << endl;
//        cout << "the sum is zero" << IsZero(aPart + bPart) << endl;
        return (aPart * a + bPart * b); //
        //return ((D[1]*TermLcm)/LT(F))*F+((D[2]*TermLcm)/LT(G))*G
    }
    
    
    //TODO: change the bool argument to a flag.
    //TODO: should ret a record instead of RingElem (maybe genetic in this case)
    //TODO: Big N and R in the name.
    // pass by ref poly.
    // raw pointer..
    // check if generators contains  zero poly.
    RemQuots nRoverZZCORE(RingElem poly, const std::vector<RingElem>& generators, bool withQuotients){
        std::vector<RingElem> quotients(generators.size());
//        cout << "nRoverZZCore: first breakpoint" << endl;
        if(IsZero(poly)) {
            if(withQuotients){
                // get rid of new(s) so you can remove the
                return  RemQuots(zero(owner(poly)), quotients);
            }
            else {
                return  RemQuots(zero(owner(poly)));
            }
        }
//        cout << "nRoverZZCore: second breakpoint" << endl;
        RingElem reminderElem(owner(poly), poly);
        bool found = true;
        while (found) {
            found = false;
            unsigned long i = 1;
//            cout << "nRoverZZCore: third breakpoint" << endl;
            while (i < generators.size() && !found) {
//                cout << "nRoverZZCore: fourth breakpoint i: " << i  << endl;
                if(
                   IsDivisible( // OF LPP , LPP
                               // here i can check if the lc is divisible the other lc, and the same for the lpp
                               monomial(owner(poly), LC(reminderElem),LPP(reminderElem)),
                               monomial(owner(poly), LC(generators.at(i)),LPP(generators.at(i))))) {
//                                   cout << "nRoverZZCore: fifth breakpoint: " << endl;
                                   // TODO: called the quotionts.at() two times.
                                   ConstRefRingElem operation = monomial(owner(poly), LC(reminderElem)/ LC(generators.at(i)) ,LPP(reminderElem) / LPP(generators.at(i)));
                                   if(IsZero(quotients.at(i))) {
                                       quotients.at(i) = operation; // the ctr of elem creates a zero element of RingZZ()
                                   }
                                   else {
                                       quotients.at(i) = quotients.at(i) + operation;
                                   }
//                    quotients.at(i) +=  //
//                                   cout << "nRoverZZCore: six breakpoint: " << endl;
                    reminderElem = sPolynomial(reminderElem, generators.at(i));
//                                   cout << "nRoverZZCore: seven breakpoint: " << endl;
                    if(IsZero(reminderElem)) {
                        if(withQuotients) {
                            return  RemQuots(zero(owner(poly)), quotients);
                        }
                        else {
                            return  RemQuots(reminderElem); // (same as putting zero)
                        }
                    }
                    found = true; // i don't think this part of the code will get executed.
                }
                i++;
            }
        }
        
        
        if(withQuotients) {
            return  RemQuots(reminderElem, quotients);
        }
        else {
            return  RemQuots(reminderElem); // this repeats a lot of times , let's create a function for this functionality.
        }
    }
    
    // Buchberger's Algoa
    std::vector<RingElem> gBasisCoreV2( std::vector<RingElem>& generators) {
//        cout<< "gBasisCoreV2: inside gBasisCoreV2" << endl;
        std::size_t length = generators.size();
        // TODO: use a set or list instead of a vector. (plus justification.)
        std::vector<SpecialPolysController> polynomials;
        polynomials.reserve(length);
        
        for(std::size_t i = 0; i < length - 1; i++) {
            for(std::size_t j = i + 1; j < length; j++) {
                const RingElem fi = generators.at(i), fj = generators.at(j);
                polynomials.push_back(SpecialPolysController(fi, fj));
            }
        }
        
        RingElem h;
        while(!polynomials.empty()) {
//            cout<<"polynomial size " << polynomials.size() << endl;
            // 4
            CheckForInterrupt("inside algo.");
//            std::this_thread::sleep_for(std::chrono::seconds(5));
            cout << "************************" << endl;
//            RingElem h = polynomials.back();
            // for (auto x: polynomials) instead of this.
            for(std::size_t i = 0; i < polynomials.size(); i++) {
                try{
                    h = polynomials[i].choose();
                }catch(UselessSpecialPoly e) {
                    // ConcurrentModificationEx.
                    // in case we checked if the spoly and gcd poly are useful and they aren't we should remove the pair and continue to the next pair.
                    // TODO: redundant code of erasing should i just keep this one and remove the isUsed method and the deleting code a put down before in the if condition.
                    // TODO: an other loop with remove_if().instead of removing it here. 
                    polynomials.erase(polynomials.begin() + i);
                    i--;
                    continue;
                }
                // TODO: make an other method that checks of the useless.
                if(polynomials[i].isUsed()) {
//                    cout << "poly size is before pop back: "  << polynomials.size() << endl ;
//                    cout << "element erased f: " << polynomials[i].getF() << ", g: " << polynomials[i].getG() << endl;
                    polynomials.erase(polynomials.begin() + i);
//                    cout << "poly size is after pop back: "  << polynomials.size() << endl;
                }
                // 5
                h = NF(h, generators);
//                cout << "result of NF: " << h << endl ;
                // 6
                if(!IsZero(h)) {
//                    cout<< " inside the condition is not zero" << endl;
    //                cout<< " polynom size before the new fill " << polynomials.size() <<endl;
                    // TODO: comment the clear intr. and test.
                    polynomials.clear();
    //                cout << "polynom size after the clear" << polynomials.size() << endl ;
                    for(auto &g : generators) {
                        polynomials.push_back(SpecialPolysController(h, g));
                    }
                    generators.push_back(h);
                    // TODO: check if the generators list is already having a strong standard represntation.
                }
    //            std::this_thread::sleep_for(std::chrono::seconds(5));
            }
        }
//        cout << "gBasisCoreV2: end of the while loop" << endl;
        return generators;
    }
    std::vector<RingElem> gBasisCore(const std::vector<RingElem>& generators) {
        // size_t.
        long length = generators.size() ;
        std::vector<std::pair<unsigned long, unsigned long>> pairList;
        for (unsigned long i = 0; i < length - 1; i++) {
            for (unsigned long j = i + 1; j < length; j++) {
                pairList.push_back(std::make_pair(i,j));
//                cout << "the pair is : (" << i << "," << j << ")" << endl;
            }
        }
//        cout << "gBasisCore: first breakpoint " << endl;
        std::vector<RingElem> gb = generators;
        while (pairList.size() > 0) {
            CheckForInterrupt("inside algo.");
            std::pair<unsigned long, unsigned long> pair = pairList.front(); // is this a copy by ref. or value ?
            // for now i ll take the first element than remove it but there is also an other way
            // I can just reverse the list and start from the last element , i should test both of this cases.
            pairList.erase(pairList.begin());
            std::vector<RingElem> polynomials;
            
//            cout << "gBasisCore: second breakpoint " << endl;
            if(isNecessaryGcdPair(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair)))) {
                RingElem polynom = gcdPolynomial(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair))); //
                if(!IsZero(polynom) && IsOne(LPP(polynom))) {
                    //TODO: sPolynomial ? in case it is already done than gcdPolynomial() ?
                    
                }
//                cout << "------------------ polynom: " << polynom << endl;
                polynomials.push_back(polynom);
            }
//            cout << "gBasisCore: third breakpoint " << endl;
            if(isNecessarySPair(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair)))) {
                polynomials.push_back(sPolynomial(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair))));
            }
//            cout << "gBasisCore: fourth breakpoint " << endl;
            for(const RingElem& poly: polynomials) {
                RingElem remainder = nRoverZZCORE(poly, gb, false).getRemainder();
//                cout << "gBasisCore: fifth breakpoint " << endl;
                if(!IsZero(remainder)){
                    if(LC(remainder) < 0) {
                        remainder = -1 * remainder;
                    }
//                    cout << "gBasisCore: sixth breakpoint " << endl;
                    gb.push_back(remainder);
                    for(unsigned long i = 0; i < gb.size() - 1; i++) {
//                        cout << "gBasisCore: seventh breakpoint with i :" << i  << endl;
                        pairList.push_back(std::make_pair(i, gb.size() - 1));
                    }
                }
            }
            
//            cout << "gBasisCore: eight breakpoint" << endl;
    
            std::sort(
                      pairList.begin(),
                      pairList.end(),
                      [gb](std::pair<unsigned long, unsigned long> a, std::pair<unsigned long, unsigned long>b){
//                          cout << "gb size is : "  << gb.size() << endl;
//                          cout << "gBasisCore: nine breakpoint, a0: " << std::get<0>(a) << " ,a1: " << std::get<1>(a) <<
//                                "b0: " <<std::get<0>(b) << ", b1: " << std::get<1>(b) << endl;
                        
                          
                return (lcm(
                           LPP(gb.at(std::get<0>(a))), LPP(gb.at(std::get<1>(a))) )
                            < lcm(LPP(gb.at(std::get<0>(b))), LPP(gb.at(std::get<1>(b))))
                        );
            });
//            cout << "gBasisCore : last breakpoint in the while" << endl;
        }
        
//        cout << "gBasisCore : last breakpoint in the gBAsiscore" << endl;
        return gb;
        
    }
    
    //maybe use the same vector so we won't need to copy the list, and also we need to make sure that the list doesn't
    // get partially filled in case an exception happend.
    
    std::vector<RingElem> gBoverZZV2(std::vector<RingElem>& v) {
        if(v.empty()){
            throw std::invalid_argument("the list must not be null");
        }
//        cout << "gBoverZZ: going to call gBasisCore(v)" << endl;
        return gBasisCoreV2(v);
    }
    std::vector<RingElem> gBoverZZ(const std::vector<RingElem>& v) {
        if(v.empty()){
            throw std::invalid_argument("the list must not be null");
        }
//        cout << "gBoverZZ: going to call gBasisCore(v)" << endl;
        return gBasisCore(v);
    }
    
    std::vector<RingElem> cleanListMZZ( std::vector<RingElem>& g){
        unsigned long length = g.size();
        if(length == 1) {
            return g;
        }
            std::sort(
                      g.begin(),
                      g.end(),
                      [g](RingElem a, RingElem b){
                          
                return (LT(a) < LT(b) or (LT(a) == LT(b) && abs(LC(a)) < abs(LC(b))));
            });
        
        std::vector<std::pair<unsigned long, unsigned long>> pairList;
        for (unsigned long i = 0; i < length - 1; i++) {
            for (unsigned long j = i + 1; j < length; j++) {
                pairList.push_back(std::make_pair(i,j));
//                cout << "the pair is : (" << i << "," << j << ")" << endl;
            }
        }
        
        for(std::pair<unsigned long, unsigned long> couple: pairList) {
            if(
               IsDivisible(LPP(g.at(std::get<0>(couple))), LPP(g.at(std::get<1>(couple)))) &&
               IsDivisible(LC(g.at(std::get<0>(couple))), LC(g.at(std::get<1>(couple))))
               ){
                   g.erase(g.begin() + std::get<1>(couple));
                   return cleanListMZZ(g);
            }
        }
        return g;
    }

    
    std::vector<RingElem> minimalGBoverZZ(const std::vector<RingElem>& v) {
        if(v.empty()) {
            throw std::invalid_argument("the list must not be null");
        }
        std::vector<RingElem> gb = gBasisCore(v);
        return cleanListMZZ(gb);
    }
    
    
  void program()
  {
    GlobalManager CoCoAFoundations;
    SignalWatcher MonitorInterrupt(SIGINT); // you must also call CheckForInterrupt every so often
      
      
    // first test of my file
      
      std::vector<RingElem> v;
      
      
      ring P = NewPolyRing(RingZZ(), symbols("x,y,z"));
      
      v.push_back(RingElem(P, "-x*y +y^2 +x +y"));
      v.push_back(RingElem(P, "-x^2 -x*y -y^2 -x-1"));
      v.push_back(RingElem(P, "-x^2 +x*y -y^2 +x +y"));
      
      // ********* time spent on gBoverZZ2 is: 0.034247, time spent on gBoverZZ is: 2.60334
//        v.push_back(RingElem(P, "x^3 - 2*x*y"));
//        v.push_back(RingElem(P, "x^2 * y - 2*y^2 + x"));
//        v.push_back(RingElem(P, "x*y-5*z"));
      
//      ********* time spent on gBoverZZ2 is: 0.001512, time spent on gBoverZZ is: 0.019121
//        v.push_back(RingElem(P, "y - z - 2 * x^2 + 3 * x - 4"));
      
      //-2*y^2*z^2 + 15*y*z^2 - 5*z;

      
      //[-2*x^2 -x*y +y^2 +2*x +2*y,  -x^2 +x*y -2*x +y -1,  x^2 -2*x*y +2*y^2 +2*x +2*y]
      
//      v.push_back(RingElem(P, "-2*x^2 -x*y +y^2 +2*x + 2*y"));
//      v.push_back(RingElem(P, "-x^2 +x*y -2*x +y -1"));
//      v.push_back(RingElem(P, "x^2 -2*x*y +2*y^2 + 2*x + 2*y"));
      //      ********* time spent on gBoverZZ2 is: undertermined , time spent on gBoverZZ is: 0.337228
      
      //[8*x^2 -5*x*y +5*y^2 +x -6*y -7,  9*x^2 -9*x*y +2*x -6*y +3,  6*x*y +y^2 +7*x +7*y +8]
        
//      v.push_back(RingElem(P, "8*x^2 -5*x*y +5*y^2 +x -6*y -7"));
//      v.push_back(RingElem(P, "9*x^2 -9*x*y +2*x -6*y +3"));
//      v.push_back(RingElem(P, "6*x*y +y^2 +7*x +7*y +8"));
      
//      cout << "finished creating the vector" << endl;

    
 
//      cout << gcdPolynomial(RingElem(P, "6 * x^2 + 1"), RingElem(P, "-4 * x^3 + 2")) << endl;
//      cout << sPolynomial(RingElem(P, "6 * x^2 + 1"), RingElem(P, "-4 * x^3 + 2")) << endl;
//
//
//
//      const clock_t begin_time1 = clock();
//      std:: vector<RingElem> resultminimum = minimalGBoverZZ(v);
//      std::cout << "tine spent on  minimal gBoverZZ is: " <<  float( clock () - begin_time1 ) /  CLOCKS_PER_SEC;
//
//      cout << " the list after the minimal gbasis thing: " << endl;
//      for(RingElem& ele: resultminimum) {
//          cout << ele << endl;
//      }

      std::vector<RingElem> gens ;

      gens.push_back(RingElem(P, "x^2 + 1 "));
      gens.push_back(RingElem(P, "x^4 -9*x*y+2*x -6*y +3")); //"x^4 -9*x*y+2*x -6*y +3"
      gens.push_back(RingElem(P, "x^2 +7*x +7*x^9 +8")); //6*x*y +y^2 +7*x +7*y +8
      // ********* time spent on gBoverZZ2 is: 0.012921, time spent on gBoverZZ is:  0.979255

      RingElem h = RingElem(P, "-x^3");

//      gens.push_back(RingElem(P, "x^2 + 1 "));
//      gens.push_back(RingElem(P, "x^4 -9*x*y+2*x -6*y +3")); //"x^4 -9*x*y+2*x -6*y +3"
//      gens.push_back(RingElem(P, "6*x*y +y^2 +7*x +7*y +8")); //6*x*y +y^2 +7*x +7*y +8
//      ********* time spent on gBoverZZ2 is: 2.09737 , time spent on gBoverZZ more than 3 min and doesn't end.
      
      
//      cout << "Test the function getElementTopReduction" << endl ;
//      ConstRefRingElem getElementTopReduction(ConstRefRingElem h, const std::vector<ConstRefRingElem>& generators){
      RingElem result10;
      BigInt a;
//      getElementTopReduction(result10, a, h, gens);
//      cout<< "Result is : " << result10 << " and a is  " << a << endl;

//      cout << "the top reduction is : " << topReduction(a, h, result10) << endl;

      cout << "the nf of h in the gens vector is " << NF(h, gens) << endl;


//      cout << "new gBoverZZ : " << endl;
//
      const clock_t begin_time2 = clock();
      std:: vector<RingElem> result2 = gBoverZZV2(v);
      std::cout << "****************time spent on gBoverZZ2 is: " <<  float( clock () - begin_time2 ) /  CLOCKS_PER_SEC << "*************" << endl;
      std::cout << "** size of the result list is : " << result2.size() << endl ;

//      cout << " the list after the new implementation of gBoverZZV2  thing: " << endl;
//      for(RingElem& ele: result2) {
//          cout << ele << endl;
//      }

      const clock_t begin_time3 = clock();
      std:: vector<RingElem> result3 = gBoverZZ(v);
      std::cout << "****************time spent on gBoverZZ is:  " <<  float( clock () - begin_time3 ) /  CLOCKS_PER_SEC << " ************* " << endl;
//      cout << " the list after the old implementation of gBoverzz" << endl;
      std::cout << "** size of the result list is : " << result3.size() << endl ;
//      for(RingElem& ele: result3) {
//          cout << ele << endl;
//      }
      
      cout << ShortDescription << endl;
    cout << boolalpha; // so that bools print out as true/false

    

  }

} // end of namespace CoCoA

//----------------------------------------------------------------------
// Use main() to handle any uncaught exceptions and warn the user about them.
int main()
{
  try
  {
    CoCoA::program();
    return 0;
  }

  catch (const CoCoA::InterruptReceived& intr)
  {
    cerr << endl
         << "------------------------------" << endl
         << ">>>  CoCoALib interrupted  <<<" << endl
         << "------------------------------" << endl
         << "-->>  " << intr << "  <<--" << endl;
    return 2;
  }
  catch (const CoCoA::ErrorInfo& err)
  {
    cerr << "***ERROR***  UNCAUGHT CoCoA error";
    ANNOUNCE(cerr, err);
  }
  catch (const std::exception& exc)
  {
    cerr << "***ERROR***  UNCAUGHT std::exception: " << exc.what() << endl;
  }
  catch(...)
  {
    cerr << "***ERROR***  UNCAUGHT UNKNOWN EXCEPTION" << endl;
  }

  CoCoA::BuildInfo::PrintAll(cerr);
  return 1;
}



// run logs::


// 22.06.2022 (rough impl. )
//8*x^2 -5*x*y +5*y^2 +x -6*y -7
//9*x^2 -9*x*y +2*x -6*y +3
//6*x*y +y^2 +7*x +7*y +8
//27*x*y +45*y^2 -7*x -6*y -87

// gBoverZZ : result in 0.016046s , minimal gBoverzz: 0.0014669s but it varies by +/- 0.002

//8*x^2 -5*x*y +5*y^2 +x -6*y -7
//9*x^2 -9*x*y +2*x -6*y +3
//6*x*y +y^2 +7*x +7*y +8
//27*x*y +45*y^2 -7*x -6*y -87
//3
//77*x +75*y +246
//26*x -1
//2
//6473
//3235
//1079
//5
//359
//2587
//1



//----------------------------------------------------------------------
// RCS header/log in the next few lines
// $Header: /Volumes/Home_1/cocoa/cvs-repository/CoCoALib-0.99/examples/ex-empty.C,v 1.16 2021/12/14 08:35:43 abbott Exp $
// $Log: ex-empty.C,v $
// Revision 1.16  2021/12/14 08:35:43  abbott
// Summary: Uncommented code for printing out "interrupted" message
//
// Revision 1.15  2020/01/09 13:32:48  abbott
// Summary: Added comment
//
// Revision 1.14  2019/11/14 17:45:59  abbott
// Summary: Added SignalWatcher (in case you want to make your code interruptible)
//
// Revision 1.13  2017/12/01 21:30:10  abbott
// Summary: Added Anna to copyright
//
// Revision 1.12  2017/07/08 19:07:02  abbott
// Summary: Removed comment out (dodgy) code for reporting unhandled interrupts
//
// Revision 1.11  2016/11/18 18:05:15  abbott
// Summary: Added commented out code to catch InterruptReceived
//
// Revision 1.10  2015/06/29 14:23:19  abbott
// Summary: added missing CoCoA:: prefix
// Author: JAA
//
// Revision 1.9  2015/06/29 13:25:54  bigatti
// -- code in namespace CoCoA
//
// Revision 1.8  2015/06/25 14:19:02  abbott
// Summary: Added call to CoCoA::BuildInfo::Printall
// Author: JAA
//
// Revision 1.7  2013/05/28 07:07:04  bigatti
// -- added "cout << boolalpha": useful for testing
//
// Revision 1.6  2012/11/30 14:04:55  abbott
// Increased visibility of comment saying "put your code here".
//
// Revision 1.5  2010/12/17 16:07:54  abbott
// Ensured that all i/o in examples is on standard C++ streams
// (rather than GlobalInput(), etc).
//
// Revision 1.4  2008/10/07 12:12:54  abbott
// Removed useless commented out #include.
//
// Revision 1.3  2007/05/31 16:06:16  bigatti
// -- removed previous unwanted checked-in version
//
// Revision 1.1.1.1  2007/03/09 15:16:11  abbott
// Imported files
//
// Revision 1.9  2007/03/07 11:51:40  bigatti
// -- improved test alignment
//
// Revision 1.8  2007/03/03 14:15:45  bigatti
// -- "foundations" renamed into "GlobalManager"
//
// Revision 1.7  2007/03/02 17:46:40  bigatti
// -- unique RingZ and RingQ
// -- requires foundations.H ;  foundations blah;  (thik of a better name)
//
// Revision 1.6  2007/03/02 10:47:53  cocoa
// First stage of RingZ modifications -- tests do not compile currently, Anna will fix this.
//
// Revision 1.5  2007/03/01 13:52:59  bigatti
// -- minor: fixed typo
//
// Revision 1.4  2007/02/28 15:15:56  bigatti
// -- minor: removed quotes in description
//
// Revision 1.3  2007/02/12 16:27:43  bigatti
// -- added strings ShortDescription and LongDescription for indexing
//
// Revision 1.2  2007/02/10 18:44:03  cocoa
// Added "const" twice to each test and example.
// Eliminated dependency on io.H in several files.
// Improved BuildInfo, and added an example about how to use it.
// Some other minor cleaning.
//
// Revision 1.1.1.1  2006/05/30 11:39:36  cocoa
// Imported files
//
// Revision 1.1  2006/03/12 21:28:34  cocoa
// Major check in after many changes
//
