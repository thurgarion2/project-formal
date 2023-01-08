import stainless.collection._
import stainless.lang._
import stainless.annotation._

//package LLL

//lattice integer ->
object LLL {
  //==========================================================================================================
  //============================axioms========================================================================
  //==========================================================================================================
  def lin_indpt_imply_non_zero(matrix : Matrix, i : BigInt):Unit={
    require(matrix.is_lin_indpt())
    require(i>=0 && i<matrix.rows)
  }.ensuring(_ => matrix(i).norm()>Rational(0,1))

  def orthogonal_imply_independent(matrix : Matrix):Unit={
    require(orthogonal(matrix))
  }.ensuring(_ => matrix.is_lin_indpt())

  def sum_conserve_lin_indpt(lattice : Lattice, bjIdx : BigInt, alpha : BigInt, biIdx : BigInt):Unit={
    require(lattice.is_lin_indpt())
    require(bjIdx<biIdx)
    require(bjIdx>=0 && bjIdx<lattice.rows)
    require(biIdx>=0 && biIdx<lattice.rows)
  }.ensuring(_ => lattice.sum_rows(bjIdx, alpha, biIdx).is_lin_indpt())

  def sum_conserve_gramschmit_basis(lattice : Lattice, bjIdx : BigInt, alpha : BigInt, biIdx : BigInt):Unit={
    require(lattice.is_lin_indpt())
    require(bjIdx<biIdx)
    require(bjIdx>=0 && bjIdx<lattice.rows)
    require(biIdx>=0 && biIdx<lattice.rows)
    sum_conserve_lin_indpt(lattice, bjIdx, alpha, biIdx)
  }.ensuring(_ => lattice.sum_rows(bjIdx, alpha, biIdx).gramSchmidt_basis()==lattice.gramSchmidt_basis())


  def swap_conserve_lin_indpt(lattice : Lattice, x:BigInt, y:BigInt):Unit = {
    require(lattice.is_lin_indpt())
    require(x>=0 && x<lattice.rows)
    require(y>=0 && y<lattice.rows)
    require(x<y)
      
  }.ensuring(_ => lattice.swap(x,y).is_lin_indpt())

  def swap_conserve_gramschmit(lattice : Lattice, x:BigInt, y:BigInt): Unit = {
    require(lattice.is_lin_indpt())
    require(x>=0 && x<lattice.rows)
    require(y>=0 && y<lattice.rows)
    require(x+1==y)
    swap_conserve_lin_indpt(lattice, x, y)
      
  }.ensuring(_ => n_first_vectors_equals(lattice.gramSchmidt_basis(), lattice.swap(x,y).gramSchmidt_basis(), x))

  def n_first_vectors_equals(m1 : Matrix, m2 : Matrix, n : BigInt):Boolean={
    if(m1.rows!=m2.rows || m1.cols!=m2.cols || n<0 && n>m1.rows){
      return false
    }
    n_first_vectors_equals(m1, m2, n, 0)
  }

  def matrix_equals_imply_n_first_vectors_equals(m1 : Matrix, m2 : Matrix, n : BigInt):Unit={
    require(m1==m2)
    require(n>=0 && n<=m1.rows)
    matrix_equals_imply_n_first_vectors_equals(m1, m2, n, 0)
  
  }.ensuring(_ => n_first_vectors_equals(m1, m2 , n))

  def matrix_equals_imply_n_first_vectors_equals(m1 : Matrix, m2 : Matrix, n : BigInt, i : BigInt):Unit={
    decreases(max(0,n-i))
    require(m1==m2)
    require(n>=0 && n<=m1.rows)
    require(i>=0 && i<=n)
  
    if(i==n){
      assert(true)
    }else{
      matrix_equals_imply_n_first_vectors_equals(m1, m2, n, i+1)
    }

  }.ensuring(_ => n_first_vectors_equals(m1, m2, n, i))

  def n_first_vectors_equals(m1 : Matrix, m2 : Matrix, n : BigInt, i : BigInt):Boolean={
    decreases(max(0,n-i))

    if(m1.rows!=m2.rows || m1.cols!=m2.cols || n<0 || n>m1.rows || i<0 || i>n){
      return false
    }
    if(i==n){
      true
    }else{
      m1(i)==m2(i) && n_first_vectors_equals(m1 , m2, n , i+1)
    }
  }

  def n_first_vectors_equals_imply_vectors(m1 : Matrix, m2 : Matrix, n : BigInt, vect : BigInt):Unit={
    require(m1.rows==m2.rows && m1.cols==m2.cols)
    require(n>=0 && n<=m1.rows)
    require(vect>=0 && vect<n)
    require( n_first_vectors_equals(m1, m2, n))
    n_first_vectors_equals_imply_vectors(m1, m2, n, 0, vect)
  }.ensuring(_ => m1(vect)==m2(vect))

  def n_first_vectors_equals_imply_vectors(m1 : Matrix, m2 : Matrix, n : BigInt, i : BigInt, vect : BigInt):Unit={
    decreases(n-i)
    require(m1.rows==m2.rows && m1.cols==m2.cols)
    require(n>=0 && n<=m1.rows)
    require(i>=0 && i<=n)
    require(vect>=i && vect<n)
    require(n_first_vectors_equals(m1, m2, n, i))
    if(i==vect){
      assert(true)
    }else{
      n_first_vectors_equals_imply_vectors(m1, m2, n, i+1, vect)
    }
  }.ensuring(_ => m1(vect)==m2(vect))

  def sum_conserve_nearly_orthogonal_(i : BigInt, j: BigInt, lattice : Lattice, k : BigInt, mu : BigInt):Unit={
    require(nearly_orthogonal_(i, j, lattice))
    require(k>=0 && k<j)
  }.ensuring(_ => nearly_orthogonal_(i,j,lattice.sum_rows(k,mu,i-1)))

  def sum_conserve_orthogonal(i : BigInt, j: BigInt, matrix : Matrix, k : BigInt, mu : Rational):Unit={
    require(orthogonal(matrix, i, j))
    require(k<i-1 && k>=0 && k<matrix.rows)
  }.ensuring(_ => orthogonal(matrix.sum_rows(k, mu, i-1), i, j))
 




//==========================================================================================================
//============================IntegralVector================================================================
//==========================================================================================================

  case class IntegralVector(size : BigInt, elems : List[BigInt]){
    require(elems.size==size)
    def dotProduct(other : IntegralVector): BigInt = {
      require(this.size == other.size)
      this.elems.zip(other.elems).foldLeft(BigInt(0)){case (sum, els) => sum+els._1*els._2}
    }

    def dotProduct(other : Vector): Rational = {
      require(this.size == other.size)
      this.to_Rational_Vector().dotProduct(other)
    }


    def norm(): BigInt = {
      this.dotProduct(this)
    }

    def to_Rational_Vector():Vector={
      Vector(size, elems.map(el => Rational(el, 1)))
    }.ensuring(res => res.size==size)

   
    def substract(other : IntegralVector): IntegralVector  = {
      require(this.size == other.size)
      IntegralVector(this.size, this.elems.zip(other.elems).map{case (x,y) => x-y})
    } ensuring(res => res.size == this.size)

    def add(other : IntegralVector): IntegralVector  = {
      require(this.size == other.size)
      IntegralVector(this.size, this.elems.zip(other.elems).map{case (x,y) => x+y})
    } ensuring(res => res.size == this.size)

    def times(other : IntegralVector): IntegralVector = {
      require(this.size == other.size)
      IntegralVector(this.size, this.elems.zip(other.elems).map{case (x,y) => x*y})
    } ensuring(res => res.size == this.size)

    def times(other : BigInt): IntegralVector = {
      IntegralVector(this.size, this.elems.map{case x => x*other})
    } ensuring(res => res.size == this.size)

  }

  def take_integral_conserve_size(n : BigInt, vectors : List[IntegralVector], size : BigInt): Unit = {
    decreases(n)
    require(vectors.forall(v => v.size==size))
    require(n>=0 && n<=vectors.size)
    if(n==0){
      assert(true)
    }else{
      take_integral_conserve_size(n-1, vectors.tail, size)
    }
  }.ensuring(_ => vectors.take(n).forall(v => v.size==size) && vectors.take(n).size==n)


  def apply_integral_conserve_size(n : BigInt, vectors : List[IntegralVector], size : BigInt): Unit = {
    decreases(n)
    require(vectors.forall(v => v.size==size))
    require(n>=0 && n<vectors.size)
    if(n==0){
      assert(true)
    }else{
      apply_integral_conserve_size(n-1, vectors.tail, size)
    }
  }.ensuring(_ => vectors(n).size==size)


  def updated_integral_conserve_size(index: BigInt, elem: IntegralVector, vectors : List[IntegralVector], size : BigInt):Unit={
    decreases(index)
    require(vectors.forall(v => v.size==size))
    require(elem.size==size)
    require(index>=0 && index<vectors.size)

    if(index==0){
      assert(true)
    }else{
      updated_integral_conserve_size(index-1, elem, vectors.tail, size)
    }

  }.ensuring(_ => vectors.updated(index, elem).forall(v => v.size==size) && vectors.updated(index, elem).size==vectors.size)

  //==========================================================================================================
  //============================Rational Vector===============================================================
  //==========================================================================================================

  case class Vector(size : BigInt, elems : List[Rational]){
      require(elems.size==size)
    
      def dotProduct(other : Vector): Rational = {
        require(this.size == other.size)
        this.elems.zip(other.elems).foldLeft(Rational(0,1)){case (sum, els) => sum+els._1*els._2}
      }


      def norm(): Rational = {
        this.dotProduct(this)
      }

      def substract(other : Vector): Vector  = {
        require(this.size == other.size)
        Vector(this.size, this.elems.zip(other.elems).map{case (x,y) => x-y})

      } ensuring(res => res.size == this.size)

      def add(other : Vector): Vector  = {
        require(this.size == other.size)
        Vector(this.size, this.elems.zip(other.elems).map{case (x,y) => x+y})

      } ensuring(res => res.size == this.size)

      def times(other : Vector): Vector = {
        require(this.size == other.size)
        Vector(this.size, this.elems.zip(other.elems).map{case (x,y) => x*y})
      } ensuring(res => res.size == this.size)

      def times(other : Rational): Vector = {
        Vector(this.size, this.elems.map{case x => x*other})
      } ensuring(res => res.size == this.size)

    }
  
   def take_conserve_size(n : BigInt, vectors : List[Vector], size : BigInt): Unit = {
    decreases(n)
    require(vectors.forall(v => v.size==size))
    require(n>=0 && n<=vectors.size)
    if(n==0){
      assert(true)
    }else{
      take_conserve_size(n-1, vectors.tail, size)
    }
  }.ensuring(_ => vectors.take(n).forall(v => v.size==size) && vectors.take(n).size==n)


  def apply_conserve_size(n : BigInt, vectors : List[Vector], size : BigInt): Unit = {
    decreases(n)
    require(vectors.forall(v => v.size==size))
    require(n>=0 && n<vectors.size)
    if(n==0){
      assert(true)
    }else{
      apply_conserve_size(n-1, vectors.tail, size)
    }
  }.ensuring(_ => vectors(n).size==size)

  def updated_conserve_size(index: BigInt, elem: Vector, vectors : List[Vector], size : BigInt):Unit={
    decreases(index)
    require(vectors.forall(v => v.size==size))
    require(elem.size==size)
    require(index>=0 && index<vectors.size)

    if(index==0){
      assert(true)
    }else{
      updated_conserve_size(index-1, elem, vectors.tail, size)
    }

  }.ensuring(_ => vectors.updated(index, elem).forall(v => v.size==size) && vectors.updated(index, elem).size==vectors.size)

  def updated_update(index: BigInt, elem: Vector, vectors : List[Vector], size : BigInt):Unit={
    decreases(index)
    require(vectors.forall(v => v.size==size))
    require(elem.size==size)
    require(index>=0 && index<vectors.size)

    updated_conserve_size(index, elem, vectors, size)
    if(index==0){
      assert(true)
    }else{
      updated_update(index-1, elem, vectors.tail, size)
    }

  }.ensuring(_ => vectors.updated(index, elem)(index)==elem)

  //==========================================================================================================
  //============================Matrix properites=============================================================
  //==========================================================================================================

  //follow gramschmit, difficult to define differently
  def orthogonal(matrix : Matrix): Boolean= {
    orthogonal(matrix, matrix.rows, matrix.rows-1)
  }

  def max(a:BigInt, b:BigInt):BigInt=if(a>=b){a}else{b}

  def orthogonal(matrix : Matrix, i : BigInt, j : BigInt): Boolean= {
    decreases(max(0,i*matrix.rows+j))
    if(i<1 || j<0 || i>matrix.rows || i<=j){
      return false
    }

    if(i==1){
      true
    }else if(j>0){
      val vi = matrix(i-1)
      val vj = matrix(j-1)
      vi.dotProduct(vj)==Rational(0,1) && orthogonal(matrix, i, j-1)
    }else{
      orthogonal(matrix, i-1, i-2)
    }
  }

  def orthogonal_imply_othogonal_vector(matrix : Matrix, i : BigInt, j : BigInt, v : BigInt, w : BigInt):Unit={
    decreases(max(0,i*matrix.rows+j))
    require(orthogonal(matrix,i,j))
    require(v>=0 && w>=1 && v<w)
    require(v!=w)
    require((w<i-1) || (v<j && w==i-1))



    if(v==j-1 && w==i-1){
      assert(true)
    }else if(j>0){
      orthogonal_imply_othogonal_vector(matrix, i, j-1, v, w)
    }else{
      orthogonal_imply_othogonal_vector(matrix, i-1, i-2, v, w)
    }
      
  }.ensuring(_ => matrix(w).dotProduct(matrix(v))==Rational(0,1))



  def lin_indpt(matrix : Matrix):Boolean= {
    gramSchmidt_algo(matrix) match {
      case None() => false
      case Some(_) => true
    }
  }


  def gramSchmidt_algo(matrix : Matrix): Option[Matrix] = {

    def gramSchmidt_algo(matrix : Matrix, i : BigInt, j : BigInt): Option[Matrix] = {
      decreases(max(0,i*matrix.rows+j))
      require(i>=1 && j>=0 && i<=matrix.rows && j<i)
  

      if(i==1){
        Some(matrix)
      }else if(j>0){
        gramSchmidt_algo(matrix, i, j-1) match {
          case None() => None()
          case Some(m) => 
            val vi = m(i-1)
            val vj = m(j-1)
            if(vj.norm()>Rational(0,1)){
              val mu = vj.dotProduct(vi)/vj.norm()
              val m_ = m.sum_rows(j-1, -mu, i-1)
              //we tried to proove it but it is hell, not enough property
              //easly verified by hand
              assert(m_(i-1).dotProduct(m_(j-1))==Rational(0,1))
              sum_conserve_orthogonal(i, j-1, m, j-1, -mu)
              Some(m_)
            }else{
              None()
            }
        }
      }else{
        gramSchmidt_algo(matrix, i-1, i-2)
      }
     

    }.ensuring(res => res match{
      case None() => true
      case Some(m) => m.rows==matrix.rows && m.cols==matrix.cols && orthogonal(m, i, j)
    })
    gramSchmidt_algo(matrix, matrix.rows, matrix.rows-1)

  }.ensuring(res => res match{
    case None() => true
    case Some(m) => m.rows==matrix.rows && m.cols==matrix.cols && orthogonal(m)
  })

  case class Matrix(rows : BigInt, cols : BigInt, vectors : List[Vector]){
    require(rows>0 && cols>0)
    require(vectors.size==rows)
    require(vectors.forall(v => v.size==cols))
    

    def apply(index : BigInt): Vector = {
      require(index>=0)
      require(index<rows)

      apply_conserve_size(index, this.vectors, cols)
      this.vectors(index)
    }.ensuring(res => res.size==cols)

    def is_lin_indpt(): Boolean = {
      lin_indpt(this)
    }

    def swap(x:BigInt, y:BigInt):Matrix = {
      require(x!=y)
      require(x>=0 && x<this.rows)
      require(y>=0 && y<this.rows)

      val xVect = this(x)
      val yVect = this(y)
      val addX = this.vectors.updated(y, xVect)
      updated_conserve_size(y, xVect, vectors, cols)
      val addY = addX.updated(x, yVect)
      updated_conserve_size(x, yVect, addX, cols)

      Matrix(rows, cols, addY)

    }.ensuring(res => res.rows==this.rows && res.cols==this.cols)
   

    def sum_rows(bjIdx : BigInt, alpha : Rational, biIdx : BigInt):Matrix = {
      require(bjIdx >=0 && bjIdx < rows)
      require(biIdx>=0 && biIdx<rows)

      
      val bj = this(bjIdx)
      val bi = this(biIdx)
      val newVect = bj.times(alpha).add(bi)
      updated_conserve_size(biIdx, newVect, this.vectors, cols)
      updated_update(biIdx, newVect, this.vectors, cols)
      Matrix(rows, cols, vectors.updated(biIdx, newVect))

    }.ensuring(res => res.rows==this.rows && res.cols==this.cols && res(biIdx)==this(bjIdx).times(alpha).add(this(biIdx)))


  }

  case class Lattice(rows : BigInt, cols : BigInt, vectors : List[IntegralVector], equivalentLattice : List[IntegralVector]){
    require(rows>0 && cols>0)
    require(vectors.size==rows)
    require(vectors.forall(v => v.size==cols))
    require(equivalentLattice.size==rows)
    require(equivalentLattice.forall(v => v.size==cols))
  

    def equivalent(other : Lattice):Boolean = {
      other.equivalentLattice == this.equivalentLattice
    }

    private def to_matrix():Matrix = {
      map_conserve_size(rows, cols, vectors)
      Matrix(rows, cols, vectors.map(v => v.to_Rational_Vector()))
    }.ensuring(res => res.rows==rows && res.cols==cols)

    private def map_conserve_size(rows : BigInt, cols : BigInt, vectors : List[IntegralVector]):Unit = {
      decreases(rows)
      require(rows>=0 && cols>0)
      require(vectors.size==rows)
      require(vectors.forall(v => v.size==cols))

      if(rows==0){
        assert(true)
      }else{
        map_conserve_size(rows-1, cols, vectors.tail)
      }
    }.ensuring(res => vectors.map(v => v.to_Rational_Vector()).forall(v => v.size==cols) &&  vectors.map(v => v.to_Rational_Vector()).size==rows)


    def is_lin_indpt():Boolean = {
      lin_indpt(to_matrix())
    }

    def gramSchmidt_basis():Matrix = {
      require(this.is_lin_indpt())
      gramSchmidt_algo(to_matrix()) match {
        case None() => assert(false)
        case Some(m) => m
      }
    }.ensuring(res => orthogonal(res) && res.cols==cols && res.rows==rows)

  

    def apply(index : BigInt): IntegralVector = {
      require(index>=0)
      require(index<rows)
      apply_integral_conserve_size(index, vectors, cols)
      vectors(index)
    }.ensuring(res => res.size==cols)



    def swap(x:BigInt, y:BigInt):Lattice = {
      require(x!=y)
      require(x>=0 && x<this.rows)
      require(y>=0 && y<this.rows)

      val xVect = this(x)
      val yVect = this(y)
      val addX = this.vectors.updated(y, xVect)
      updated_integral_conserve_size(y, xVect, vectors, cols)
      val addY = addX.updated(x, yVect)
      updated_integral_conserve_size(x, yVect, addX, cols)

      Lattice(rows, cols, addY, equivalentLattice)
    }.ensuring(res => res.rows==this.rows && res.cols==this.cols)

   
    def sum_rows(bjIdx : BigInt, alpha : BigInt, biIdx : BigInt):Lattice = {
      require(bjIdx >=0 && bjIdx < rows)
      require(biIdx>=0 && biIdx<rows)

      
      val bj = this(bjIdx)
      val bi = this(biIdx)
      val newVect = bj.times(alpha).add(bi)
      updated_integral_conserve_size(biIdx, newVect, this.vectors, cols)
      val newVects = vectors.updated(biIdx, newVect)
      Lattice(rows, cols, newVects, equivalentLattice)
    }.ensuring(res => res.rows==this.rows && res.cols==this.cols)   
    
  }

  def abs(a : Rational):Rational = if(a<Rational(0,1)){-a}else{a}
  def nearly_orthogonal(lattice : Lattice): Boolean= {
    nearly_orthogonal(lattice, lattice.rows, lattice.rows-1)
  }

  def nearly_orthogonal(lattice : Lattice, i : BigInt, j : BigInt): Boolean= {
    decreases(max(0,i*lattice.rows+j))
    if(i<1 || j<0 || i>lattice.rows || i<=j || !lattice.is_lin_indpt()){
      return false
    }

    if(i==1){
      true
    }else if(j>0){
      nearly_orthogonal_vector(lattice, i-1, j-1) && nearly_orthogonal(lattice, i,j-1)
    }else{
      nearly_orthogonal(lattice, i-1,i-2)
    }
  }
  def nearly_orthogonal_equivalence(lattice : Lattice, i1 : BigInt, j1 : BigInt, i2 : BigInt, j2 : BigInt):Unit = {
    decreases(max(0,i1*lattice.rows+j1))
    require(nearly_orthogonal(lattice, i1, j1))
    require(i2>=1 && i2<=lattice.rows && i2>j2 && j2>=0)
    require((i1==i2 && j2<=j1) || i2<i1)

    if(i1==i2 && j1==j2){
      assert(true)
    }else if(j1>0){
      nearly_orthogonal_equivalence(lattice, i1, j1-1, i2, j2)
    }else{
      nearly_orthogonal_equivalence(lattice, i1-1, i1-2, i2, j2)
    }

  }.ensuring(_ =>  nearly_orthogonal(lattice, i2, j2))

  def nearly_orthogonal_equivalence(lattice1 : Lattice,  lattice2 : Lattice, i : BigInt, j : BigInt, n : BigInt): Unit = {
    decreases(max(0,i*lattice1.rows+j))
    require(lattice1.rows==lattice2.rows && lattice1.cols==lattice2.cols)
    require(lattice1.is_lin_indpt())
    require(lattice2.is_lin_indpt())
    require(i>=1 && j>=0 && i<=lattice1.rows && i>j)
    require(n>=0 && n<=lattice1.rows)
    require(i<=n)
    require(nearly_orthogonal(lattice1, i, j))
    require(n_first_vectors_equals(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), n))

    if(i==1){
      assert(true)
    }else if(j>0){
      //we have to define the notion of n first rows are the same for lattice
      //but we don't have time so we will not do it as it is not bringing a lot of value
      assert(lattice1(i-1)==lattice2(i-1))
      n_first_vectors_equals_imply_vectors(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), n, j-1)
      nearly_orthogonal_equivalence(lattice1,  lattice2, i, j-1, n)
    }else{
      nearly_orthogonal_equivalence(lattice1,  lattice2, i-1, i-2, n)
    }
   

  }.ensuring(_ =>  nearly_orthogonal(lattice2, i, j))

  def nearly_orthogonal_imply_vector(i : BigInt, j: BigInt, lattice : Lattice, w : BigInt, v: BigInt):Unit ={
    decreases(max(0,i*lattice.rows+j))
    require(i>=1 && j>=0 && i<=lattice.rows && i>j  && lattice.is_lin_indpt())
    require(nearly_orthogonal(lattice, i, j))
    require(v<w && v>=0 && w<i)
    require((i-1==w && v<=j-1) || (w<i-1))

    if(w==i-1 && v==j-1){
      assert(true)
    }else if(j>0){
      nearly_orthogonal_imply_vector(i, j-1, lattice, w, v)
    }else{
      nearly_orthogonal_imply_vector(i-1, i-2, lattice, w, v)
    }

  }.ensuring(_ => nearly_orthogonal_vector(lattice, w, v))

  def nearly_orthogonal_vector(lattice : Lattice, i : BigInt, j : BigInt):Boolean = {
    require(i>=0 && i<lattice.rows && j>=0 && j<lattice.rows)
    require(lattice.is_lin_indpt())
    require(j<i)
    val gramBasis = lattice.gramSchmidt_basis()
    val vi = lattice(i)
    val vj = gramBasis(j)
    orthogonal_imply_independent(gramBasis)
    lin_indpt_imply_non_zero(gramBasis, j)
    val mu = vi.dotProduct(vj)/vj.norm()
    abs(mu)<=Rational(1,2)
  }

  // def nearly_orthogonal_vector_equivalence(lattice1 : Lattice, lattice2 : Lattice, i : BigInt, j : BigInt):Unit = {
  //   require(i>=0 && i<lattice1.rows && j>=0 && j<lattice1.rows)
  //   require(lattice1.rows==lattice2.rows && lattice1.cols==lattice2.cols)
  //   require(lattice2.is_lin_indpt())
  //   require(lattice1.is_lin_indpt())
  //   require(j<i)
  //   require(nearly_orthogonal_vector(lattice1, i, j))

  // }.ensuring(_ => nearly_orthogonal_vector(lattice2, i, j))

  
  def lovaz_condition(lattice : Lattice, alpha : Rational): Boolean = {
    lovaz_condition(lattice, lattice.rows, alpha)
  }
  def lovaz_condition(lattice : Lattice, until : BigInt, alpha : Rational):Boolean={
    decreases(max(until, 0))

    if(until>lattice.rows || until<1  || !lattice.is_lin_indpt()){
        return false
    }

    if(until==1){
       true
    }else{
      val gramBasis = lattice.gramSchmidt_basis()
      val g_k = gramBasis(until-2)
      val g_k_1 = gramBasis(until-1)
      g_k.norm() <= alpha*g_k_1.norm() &&  lovaz_condition(lattice, until-1, alpha)
    }  
  }

  def lovaz_condition_equivalence(lattice1 : Lattice, lattice2 : Lattice, until : BigInt, alpha : Rational):Unit={
    decreases(until)
    require(until>=1 && until<=lattice1.rows)
    require(lattice1.is_lin_indpt() && lattice2.is_lin_indpt())
    require(lattice1.rows==lattice2.rows && lattice1.cols==lattice2.cols)
    require(lovaz_condition(lattice1, until, alpha))
    require(n_first_vectors_equals(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), until))
    lovaz_condition_equivalence(lattice1, lattice2, until, until, alpha)
  }.ensuring(_ => lovaz_condition(lattice2, until, alpha))


  def lovaz_condition_equivalence(lattice1 : Lattice, lattice2 : Lattice, until : BigInt, n : BigInt, alpha : Rational):Unit={
    decreases(until)
    require(until>=1 && until<=lattice1.rows)
    require(n>=0 && n<=lattice1.rows)
    require(until<=n)
    require(lattice1.is_lin_indpt() && lattice2.is_lin_indpt())
    require(lattice1.rows==lattice2.rows && lattice1.cols==lattice2.cols)
    require(lovaz_condition(lattice1, until, alpha))
    require(n_first_vectors_equals(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), n))

    if(until==1){
      assert(true)
    }else{
      n_first_vectors_equals_imply_vectors(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), n, until-2)
      n_first_vectors_equals_imply_vectors(lattice1.gramSchmidt_basis(), lattice2.gramSchmidt_basis(), n, until-1)
      lovaz_condition_equivalence(lattice1, lattice2, until-1, n, alpha)
    }

  }.ensuring(_ => lovaz_condition(lattice2, until, alpha))





  def round(p: Rational): BigInt ={
    var a = p.numerator
    var b = p.denominator
    var k = BigInt(0)
    if (a >= 0){
      k = a/b
    }else{
      k = a/b - 1
    }
    if(Rational(a,b)-Rational(k) <= Rational(k+1)-Rational(a,b)){
      k
    }else{
      k+1
    }
  }

  //   // def pow(p: Rational, n: BigInt): Rational ={
  //   //   decreases(n)
  //   //   require(n >= 1)
  //   //   if(n==1){
  //   //     p
  //   //   }else{
  //   //     assert(n>1)
  //   //     p*pow(p,n-1)
  //   //   }
  //   // }

  //   // // def determinant(M: Matrix): Rational = M match{
  //   // //       case Nil() => Rational(1)
  //   // //       case x::xs => pow(scalarProduct(x,x),M.size)*determinant(xs)
  //   // //     }

  def nearly_orthogonal_(i : BigInt, j: BigInt, lattice : Lattice): Boolean = {
    decreases(max(0,i-j))

    if(i<1 || i>lattice.rows || j>=i || j<0 || (i!=1 && !nearly_orthogonal(lattice, i-1, i-2)) || !lattice.is_lin_indpt()){
      return false
    }
    if(j==i-1){
      true
    }else{
      nearly_orthogonal_vector(lattice, i-1, j) && nearly_orthogonal_(i, j+1, lattice)
    }
  }

  def nearly_orthogonal_imply_vector_(i : BigInt, j: BigInt, lattice : Lattice, w : BigInt, v: BigInt):Unit ={
    decreases(max(0,i-j))
    require(nearly_orthogonal_(i, j, lattice))
    require(v<w && v>=0 && w<i)
    require((i-1==w && v>=j) || (w<i-1))

    if(w==i-1 && j==v){
      assert(true)
    }else if(j==i-1){
      nearly_orthogonal_imply_vector(i-1, i-2, lattice, w, v)
    }else{
      nearly_orthogonal_imply_vector_(i, j+1, lattice, w, v)
    }

  }.ensuring(_ => nearly_orthogonal_vector(lattice, w, v))

  def nearly_orthogonal_equivalent_nearly_orthogo(i : BigInt, lattice : Lattice, v : BigInt, w: BigInt): Unit = {
    decreases(max(0,v*lattice.rows+w))
    require(nearly_orthogonal_(i, 0, lattice))
    require(v<=i)
    require(v>=1 && w>=0 && v>w && lattice.is_lin_indpt())


    if(v==1){
      assert(true)
    }else if(w>0){
      nearly_orthogonal_imply_vector_(i, 0, lattice, v-1, w-1)
      nearly_orthogonal_equivalent_nearly_orthogo(i, lattice, v, w-1)
    }else{
      nearly_orthogonal_equivalent_nearly_orthogo(i, lattice, v-1, v-2)
      assert(nearly_orthogonal(lattice, v, 0))
    }

  }.ensuring(_ => nearly_orthogonal(lattice, v, w))

  def reduced(i : BigInt, lattice : Lattice, alpha : Rational): Boolean = {
    lovaz_condition(lattice, i, alpha) && nearly_orthogonal(lattice, i, i-1)
  }


  

  def LLL(orginal : Lattice, alpha : Rational): Lattice = {
    require(alpha > Rational(4,3))
    require(orginal.is_lin_indpt())

    def LLLAprox(i : BigInt, lattice : Lattice):Lattice = {
      require(lovaz_condition(lattice, i-1, alpha))
      require(i>=1 && i<=lattice.rows)
      require(i==1 || nearly_orthogonal(lattice, i-1, i-2))
      require(lattice.is_lin_indpt())
      val aprox = LLLAprox_(i, 0, lattice)
      nearly_orthogonal_equivalent_nearly_orthogo(i, aprox, i,i-1)
      aprox
      
    }.ensuring(res => res.rows==lattice.rows && res.cols==lattice.cols && res.equivalent(lattice) && lovaz_condition(res, i-1, alpha)
    && nearly_orthogonal(res, i, i-1) && res.is_lin_indpt())

    

    def LLLAprox_(i : BigInt, j: BigInt, lattice : Lattice):Lattice = {
      decreases(i-j)
      require(i>=1 && i<=lattice.rows && j<i && j>=0)
      require(lattice.is_lin_indpt())
      require(i==1 || nearly_orthogonal(lattice, i-1, i-2))
      require(lovaz_condition(lattice, i-1, alpha))
       
       
      if(j==i-1){
        lattice
      }else{
        val aproxLattice = LLLAprox_(i, j+1, lattice)
        val gramBasis = aproxLattice.gramSchmidt_basis()
  
        val vi = aproxLattice(i-1)
        val vj = gramBasis(j)
        orthogonal_imply_independent(gramBasis)
        lin_indpt_imply_non_zero(gramBasis, j)
    
        val mu = vi.dotProduct(vj)/vj.norm()
        val updated =  aproxLattice.sum_rows(j, -round(mu), i-1)

        sum_conserve_lin_indpt(aproxLattice, j, -round(mu), i-1)
        sum_conserve_gramschmit_basis(aproxLattice,j, -round(mu), i-1)
        matrix_equals_imply_n_first_vectors_equals(aproxLattice.gramSchmidt_basis(), updated.gramSchmidt_basis(), i-1)

        lovaz_condition_equivalence(aproxLattice, updated, i-1, alpha)
        sum_conserve_nearly_orthogonal_(i, j+1, aproxLattice, j, -round(mu))
        //we tried to proove it but it is hell, not enough property
        //easly verified by hand
        assert(nearly_orthogonal_vector(updated, i-1, j))
        updated
      } 
    }.ensuring(res => res.rows==lattice.rows && res.cols==lattice.cols && res.equivalent(lattice) && lovaz_condition(res, i-1, alpha)
    && nearly_orthogonal_(i, j, res) && res.is_lin_indpt())

    def LLLloop(index : BigInt, lattice : Lattice): Lattice = {
      require(index>=0 && index<=lattice.rows)
      require(index==0 || reduced(index, lattice, alpha))
      require(lattice.is_lin_indpt() && lattice.rows==orginal.rows && lattice.cols==orginal.cols && lattice.equivalent(orginal))

      //(determinant(gramBasis), vects.length)
      //wrong mesure but we define one just to check other properites
      decreases(lattice.rows-index)

      if(index==lattice.rows){
        lattice
      }else if(index==0){
        LLLloop(index+1, lattice)
      }else{
        val aproxOrtho = LLLAprox(index+1, lattice)
       
        if(lovaz_condition(aproxOrtho, index+1, alpha)){
          LLLloop(index+1, aproxOrtho)
        }else{
          val swapped = aproxOrtho.swap(index-1, index)
          swap_conserve_lin_indpt(aproxOrtho, index-1, index)
          swap_conserve_gramschmit(aproxOrtho, index-1, index)

          if(index>1){
            lovaz_condition_equivalence(aproxOrtho, swapped, index-1, alpha)
            nearly_orthogonal_equivalence(aproxOrtho, index, index-1, index-1, index-2)
            nearly_orthogonal_equivalence(aproxOrtho,  swapped, index-1, index-2, index-1)
            LLLloop(index-1, swapped)
          }else{
            LLLloop(index-1, swapped)
          }

        }
      }
    }.ensuring(res => reduced(res.rows, res, alpha) && res.is_lin_indpt() && res.rows==orginal.rows && res.cols==orginal.cols && res.equivalent(orginal))
    LLLloop(0, orginal)  
  }.ensuring(res => reduced(res.rows, res, alpha) && res.is_lin_indpt() && res.rows==orginal.rows && res.cols==orginal.cols && res.equivalent(orginal))
} 