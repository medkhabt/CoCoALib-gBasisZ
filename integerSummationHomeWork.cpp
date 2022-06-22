// Copyright (c) 2006  John Abbott,  Anna M. Bigatti
// This file is part of the CoCoALib suite of examples.
// You are free to use any part of this example in your own programs.

#include "CoCoA/library.H"

using namespace std;

//----------------------------------------------------------------------
const string ShortDescription =
  "this file is to solve the exercice of getting the sum of a vector and of creating a class that do the summation  \n"
  "The program itself does nothing whatsoever.    \n";

const string LongDescription =
  "Make a copy of this file (called \"foo.C\", say) and put your code \n"
  "inside the procedure \"program\".                                  \n"
  "To compile your file in the examples directory just do this:       \n"
  "  make foo                                                         \n";
//----------------------------------------------------------------------

namespace CoCoA
{


    class IntegerSum
    {
            
        public:
            BigInt sum;
            IntegerSum()
            {
                sum = BigInt(0);
            }
            void addBigInt(const BigInt &number)
            {
                sum += number;
            }
    };
    void computeSumOfBigIntVector(const std::vector<BigInt> &vectorBigInt)
    {
        BigInt sum(0);
        for(auto const &i : vectorBigInt) {
            sum += i;
        }
        std::cout << " the sum of the vector is " + FloatStr(sum);
    }
    void program()
    {
        GlobalManager CoCoAFoundations;
        SignalWatcher MonitorInterrupt(SIGINT); // you must also call CheckForInterrupt every so often

        cout << ShortDescription << endl;
        cout << boolalpha; // so that bools print out as true/false
        std::vector<BigInt> numbers;
        numbers.push_back(BigInt(1000000000));
        numbers.push_back(BigInt(10000000));
        numbers.push_back(BigInt(500000000));
        computeSumOfBigIntVector(numbers);
        
        IntegerSum* sumWithClass = new IntegerSum();
        sumWithClass->addBigInt(BigInt(1000000000));
        sumWithClass->addBigInt(BigInt(2000000000));
        sumWithClass->addBigInt(BigInt(3000000000));
        std::cout << " the sum using the class is " + FloatStr(sumWithClass->sum);
      

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
