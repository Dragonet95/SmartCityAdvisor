 /* Signatures */

 /*Every person is possibly assigned to a position, 
 whether they are Guests, Users or Superusers*/
 abstract sig Person{
	currentPos: lone Position
 }

 sig Position{}
 sig Text{}

 /*Current traffic status, R G Y*/
 sig Status{}
 one sig Red extends Status{}
 one sig Yellow extends Status{}
 one sig Green extends Status{}

 /*ID is one and assigned randomly, 
 mostly to keep the world "easier" to read*/
 sig randomID{}
 {#randomID=1}

 sig Time{
    hour: one Int,
    day: one Int,
    month: one Int,
    year: one Int
 }
 {
	hour>0
	day>0
	month>0
	year>0
 }

 sig TrafficLight {}

 /*Basic components managed by the system*/

 sig Actuator{
	hasID: one randomID,
	refersTo: one TrafficLight
 }

 sig Sensor{
	hasID: one randomID,
	hasValue: one Int
 }
 {
	hasValue>0
 }

 sig Display{
	hasID: one randomID
 }

 /*Users Hierarchy: SuperUser>User>Guest*/

 sig Guest extends Person{
	tempID: one randomID
 }

 sig User extends Guest{
	 username: one Text,
    reservations: set Reservation,
	 receives: set ParkingSuggestions
 }

 sig SuperUser extends User{
 }

 /*Registered Users Reservations, multiples allowed*/
 sig Reservation{
	position: one Position,
	lot: one ParkingLot,
	time: one Time
 }

 /*Represents the internal system*/
 sig System {
   currentStatus: one Status,
   	managing: set Actuator,
	showing: set Display,
	sensors: set Sensor,
	news: lone News
 }

 /*Possible reprentation of events, news are multiple events*/
 /*Events Hierarchy*/

 abstract sig Event{
    start: one Time,
    end: one Time,
	addedBy: one SuperUser
 }
 {
	start != end
	start.year=end.year
	start.month=end.month
	end.day=start.day
	end.hour>start.day
 }

 sig SpecialEvent extends Event{
    title: one Text,
    desc: one Text,
    position: one Position
 }

 sig Emergency extends Event{
    type: one Text,
    position: one Position
 }

 sig News {
    events: set Event
 }

 /*Every suggestion is the system answering with
 multiple possible parking lots near you, user may 
 ask many times for a suggestion*/
 sig ParkingLot {
    parkingPosition: one Position,
    distance: one Int,
    spots: one Int
 }
 {
	spots>0
	distance>0
 }

 sig ParkingSuggestions {
    suggestions: some ParkingLot
 }


 /* Facts */

 /*Unique Usernam is required */
 fact UniqueUsername{
	no disjoint u1,u2: User | u1.username = u2.username
 }

 /*If user made a reservation he certantly asked
 for a suggestion*/
 fact reservationImplySuggestion{
	all u: User |
	#u.reservations < #u.receives
 }

 /*Can't have two reservations on the same parking lot
 for a single user*/
 fact noDoubleReservations{
	all u: User |
	no disj x,y: u.reservations | x.position=y.position
 }

 /*Number of actuators and traffic lights should be the same,
 at least the active working ones*/
 fact actuatorHasTrafficLight{
	#Actuator = #TrafficLight
 }

 /*Two actuators can't refer to the same traffic light*/
 fact noDoubleActuator {
	no disj a1,a2: Actuator | a1.refersTo = a2.refersTo
 }

 /*System shouldn't suggest the same parking lot twice
 when asked for suggestions*/
 fact noDoubleSuggestion {
	all u: User |
	no disj x,y: u.receives.suggestions | x.parkingPosition=y.parkingPosition
 }

 /*Can't have different parking lots in the same position*/
 fact differentPosParking{
	no disj p1,p2: ParkingLot | p1.parkingPosition = p2.parkingPosition
 }

 /*Events can't overlap*/
 fact disjointEvents{
	all disj e1,e2: Event | 
	e2.start.year=e1.start.year &&
	e2.start.month=e1.start.month &&
	e2.start.day=e1.start.day &&
	(((e1.start).hour)>((e2.end).hour) ||
	((e2.start).hour) > ((e1.end).hour))
 }

 /*Some possible bindings*/
 fact Bindings {
	all u: User, r: Reservation | r in u.reservations
	all s: System, se: Sensor | se in s.sensors
	all s: System, n: News | n in s.news
	all s: System, a: Actuator | a in s.managing
	all s: System, d: Display | d in s.showing
 }

 /* Assertion */

 assert DisjointEvents{
	no disj e1,e2: Event | 
	e2.start.year=e1.start.year &&
	e2.start.month=e1.start.month &&
	e2.start.day=e1.start.day &&
	(( e2.start.hour>e1.start.hour && e2.start.hour < e1.end.hour ) ||
	( e2.end.hour>e1.start.hour && e2.end.hour < e1.end.hour))
 }

 /* Predicate */

 /*A possible world may have the following signatures*/
 pred generateWorld{
	#System = 1
	#User = 2
	#Reservation = 2
	#Emergency = 1
	#SpecialEvent = 1
 }

 check DisjointEvents for 3
 run generateWorld for 3
