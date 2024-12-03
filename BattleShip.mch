/* BattleShip
 * Author: hirun
 * Creation date: 12/3/2024
 */
MACHINE BattleshipsGame
SETS
    PLAYERS = {Player1, Player2}
CONSTANTS
    GRID_DIMENSION, MAX_SHIPS, VALID_POSITIONS
PROPERTIES
    GRID_DIMENSION = 10 &
    MAX_SHIPS = 3 &
    VALID_POSITIONS = 1..GRID_DIMENSION × 1..GRID_DIMENSION
VARIABLES
    fleet, shots, current_turn, game_status
INVARIANT
    fleet : PLAYERS --> FIN(VALID_POSITIONS) &
    shots : PLAYERS --> FIN(VALID_POSITIONS) &
    ∀p.(p ∈ PLAYERS => card(fleet(p)) <= MAX_SHIPS) &
    current_turn ∈ PLAYERS &
    game_status ∈ {"ongoing", "player1_win", "player2_win", "deploying"}
INITIALISATION
    fleet := {} ||
    shots := {} ||
    current_turn := Player1 ||
    game_status := "deploying"
OPERATIONS
    deployFleet(player, positions) =
    PRE
        game_status = "deploying" &
        positions ⊆ VALID_POSITIONS &
        #(positions) = MAX_SHIPS &
        ∀p.(p : PLAYERS ⇒ player /= p ⇒ positions ∩ fleet(p) = {})
    THEN
        fleet(player) := positions ||
        IF #(fleet(Player1)) = MAX_SHIPS & #(fleet(Player2)) = MAX_SHIPS THEN
            game_status := "ongoing"
        END
    END;

    playerShoots(target) =
    PRE
        game_status = "ongoing" &
        target : VALID_POSITIONS &
        target /: shots(current_turn)
    THEN
        shots(current_turn) := shots(current_turn) ∪ {target} ||
        IF target : fleet(opponent(current_turn)) THEN
            fleet(opponent(current_turn)) := fleet(opponent(current_turn)) - {target} ||
            IF #(fleet(opponent(current_turn))) = 0 THEN
                game_status := current_turn = Player1 ? "player1_win" : "player2_win"
            ELSE
                current_turn := opponent(current_turn)
            END
        ELSE
            current_turn := opponent(current_turn)
        END
    END;

    shipLocations(player) =
    BEGIN
        RESULT := fleet(player)
    END;

    shipsLeft =
    BEGIN
        RESULT := {p | p : PLAYERS | #(fleet(p))}
    END;

    shotsTaken(player) =
    BEGIN
        RESULT := #(shots(player))
    END;

    gameStatus =
    BEGIN
        RESULT := game_status
    END;

    opponent(player) =
    BEGIN
        RESULT := player = Player1 ? Player2 : Player1
    END
END
