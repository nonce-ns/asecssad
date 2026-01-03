local startTime = os.clock()
repeat task.wait(0.5) until (_G.Forge and _G.Forge.Tabs and _G.Forge.Tabs.Player and _G.Forge.Rayfield)
    or (os.clock() - startTime) > 10

if not (_G.Forge and _G.Forge.Tabs and _G.Forge.Tabs.Player and _G.Forge.Rayfield) then
    warn("[Sell] Dependencies not ready; aborting load")
    return
end

-- ═══════════════════════════════════════════════════════════════════════════
-- SERVICES
-- ═══════════════════════════════════════════════════════════════════════════

local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local RunService = game:GetService("RunService")
local GuiService = game:GetService("GuiService")
local Workspace = game:GetService("Workspace")

local LocalPlayer = Players.LocalPlayer
local Forge = _G.Forge
local Rayfield = Forge.Rayfield

-- ═══════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ═══════════════════════════════════════════════════════════════════════════

local DefaultConfig = {
    AutoSell = false,
    SellInterval = 30,
    SellCooldown = 2,
    SkipFavorites = true,
    NoTeleportAfterFirst = true, -- after first success, try without teleport; if dialog fails, skip instead of teleporting
}

local Config = {}
for k, v in pairs(DefaultConfig) do
    Config[k] = v
end

Forge.SellConfig = Config
Forge.SellDefaultConfig = DefaultConfig

-- ═══════════════════════════════════════════════════════════════════════════
-- STATE VARIABLES
-- ═══════════════════════════════════════════════════════════════════════════

local AutoSellThread = nil
local LastSellTime = 0
local IsSelling = false
local HasInitializedSell = false  -- First sell needs teleport, after that skip

if LocalPlayer then
    LocalPlayer.CharacterAdded:Connect(function()
        HasInitializedSell = false
    end)
end

-- Fly system state
local MagicCarpet = nil
local BodyGyro = nil
local FlyConnection = nil
local NoClipConnection = nil
local IsFlying = false
local FLY_SPEED = 20
local CARPET_OFFSET = -3.5
local STOP_DISTANCE = 8

-- ═══════════════════════════════════════════════════════════════════════════
-- DATA TABLES
-- ═══════════════════════════════════════════════════════════════════════════

local EssenceNames = {
    ["Tiny Essence"] = true,
    ["Small Essence"] = true,
    ["Medium Essence"] = true,
    ["Large Essence"] = true,
    ["Greater Essence"] = true,
    ["Superior Essence"] = true,
    ["Epic Essence"] = true,
    ["Legendary Essence"] = true
}

local DoNotSell = {
    SimpleLantern = true,
    PortalTool = true,
    ChristmasEventCurrency = true,
    Misc = true,
    Equipments = true,
}

-- ═══════════════════════════════════════════════════════════════════════════
-- HELPER FUNCTIONS
-- ═══════════════════════════════════════════════════════════════════════════

local function Log(msg)
    print("[Sell] " .. msg)
    if _G.Forge and _G.Forge.Log then
        _G.Forge.Log("[Sell] " .. msg)
    end
end

local function Notify(title, content, duration)
    pcall(function()
        Rayfield:Notify({
            Title = title,
            Content = content,
            Duration = duration or 2
        })
    end)
end

local function ResetDashValue(container, key)
    if type(container) ~= "table" then return false end
    local value = rawget(container, key)
    if type(value) == "number" then
        container[key] = 0
        return true
    end
    if type(value) == "boolean" then
        container[key] = false
        return true
    end
    return false
end

local function ResetDashState(movement)
    if type(movement) ~= "table" then return false end
    local changed = false
    if ResetDashValue(movement, "DashCooldown") then changed = true end
    if ResetDashValue(movement, "Dashing") then changed = true end
    return changed
end

local function ShouldClearStatusBool(name)
    if type(name) ~= "string" then return false end
    local lower = name:lower()
    return lower == "nomovement"
        or lower == "disablebackpack"
        or lower == "nodash"
        or lower == "disabledash"
        or lower == "nodashcooldown"
end

-- DialogueRemote tap to avoid missed events
local LastDialogueRoot = {root = nil, ctx = nil, time = 0}
local DialogueTapConn = nil
local CachedConfirmCtx = nil
local CachedConfirmTime = 0

local function EnsureDialogueTap()
    if DialogueTapConn and DialogueTapConn.Connected then return end
    local dlgRemote = ReplicatedStorage:FindFirstChild("DialogueRemote", true)
    if not dlgRemote then return end
    DialogueTapConn = dlgRemote.OnClientEvent:Connect(function(root, ctx)
        LastDialogueRoot.root = root
        LastDialogueRoot.ctx = ctx
        LastDialogueRoot.time = os.clock()
        if root == "SellConfirmMisc" then
            CachedConfirmCtx = ctx
            CachedConfirmTime = os.clock()
        end
    end)
end

-- Wait for DialogueRemote to deliver a specific root (e.g., SellConfirmMisc)
local function WaitForDialogueRoot(targetRoot, timeout)
    EnsureDialogueTap()
    local dlgRemote = ReplicatedStorage:FindFirstChild("DialogueRemote", true)
    if not dlgRemote or not targetRoot then return false, nil end

    local start = os.clock()
    local limit = timeout or 2

    -- If already seen recently, return immediately
    if LastDialogueRoot.root == targetRoot and (os.clock() - LastDialogueRoot.time) <= limit then
        return true, LastDialogueRoot.ctx
    end

    local received = false
    local receivedCtx = nil
    local conn
    conn = dlgRemote.OnClientEvent:Connect(function(root, ctx)
        if root == targetRoot then
            received = true
            receivedCtx = ctx
        end
    end)

    while not received and (os.clock() - start) < limit do
        task.wait(0.05)
        if LastDialogueRoot.root == targetRoot and (os.clock() - LastDialogueRoot.time) <= limit then
            received = true
            receivedCtx = LastDialogueRoot.ctx
        end
    end

    if conn then conn:Disconnect() end
    return received, receivedCtx
end

local function TryReuseCachedConfirm(remotes)
    if not CachedConfirmCtx then return false end
    if (os.clock() - CachedConfirmTime) > 120 then
        return false
    end
    Log("Reusing cached SellConfirm context (no teleport)")
    if remotes and remotes.DialogueEvent then
        pcall(function() remotes.DialogueEvent:FireServer("Opened") end)
    end
    return true
end

local function ToggleDialogueHandler(disable)
    local playerGui = LocalPlayer:FindFirstChild("PlayerGui")
    if not playerGui then return end
    local dialogueUI = playerGui:FindFirstChild("DialogueUI")
    if not dialogueUI then return end
    local handler = dialogueUI:FindFirstChild("DialogueHandler")
    if handler and handler:IsA("LocalScript") then
        pcall(function()
            handler.Disabled = disable and true or false
        end)
    end
end

-- ═══════════════════════════════════════════════════════════════════════════
-- REMOTES
-- ═══════════════════════════════════════════════════════════════════════════

local function GetRemotes()
    local shared = ReplicatedStorage:FindFirstChild("Shared")
    local packages = shared and shared:FindFirstChild("Packages")
    local knit = packages and packages:FindFirstChild("Knit")
    local services = knit and knit:FindFirstChild("Services")
    
    local proximityService = services and services:FindFirstChild("ProximityService")
    local dialogueService = services and services:FindFirstChild("DialogueService")

    local proximityRF = proximityService and proximityService:FindFirstChild("RF")
    local dialogueRF = dialogueService and dialogueService:FindFirstChild("RF")
    local dialogueRE = dialogueService and dialogueService:FindFirstChild("RE")

    return {
        ForceDialogue = proximityRF and proximityRF:FindFirstChild("ForceDialogue"),
        Dialogue = proximityRF and proximityRF:FindFirstChild("Dialogue"),
        RunCommand = dialogueRF and dialogueRF:FindFirstChild("RunCommand"),
        DialogueEvent = dialogueRE and dialogueRE:FindFirstChild("DialogueEvent")
    }
end

local function GetNPC()
    local proximity = Workspace:FindFirstChild("Proximity")
    return proximity and proximity:FindFirstChild("Greedy Cey")
end

-- ═══════════════════════════════════════════════════════════════════════════
-- PLAYER DATA RETRIEVAL - Search for tables with Inventory directly
-- ═══════════════════════════════════════════════════════════════════════════

local function IsLocalUserId(value)
    local userId = LocalPlayer and LocalPlayer.UserId
    if not userId then return false end
    if value == userId then return true end
    local numberValue = tonumber(value)
    return numberValue == userId
end

local function InventoryLooksValid(inv)
    if type(inv) ~= "table" then return false end
    if type(rawget(inv, "Misc")) == "table" or type(rawget(inv, "Equipments")) == "table" then
        return true
    end
    for k, v in pairs(inv) do
        if type(k) == "string" and (type(v) == "number" or type(v) == "table") then
            return true
        end
    end
    return false
end

local function FindPlayerDataInObjects(objects)
    local fallback = nil
    for _, obj in pairs(objects) do
        if type(obj) == "table" then
            local data = rawget(obj, "Data")
            if type(data) == "table" then
                local inv = rawget(data, "Inventory")
                if type(inv) == "table" then
                    local tags = rawget(obj, "Tags")
                    if type(tags) == "table" and IsLocalUserId(rawget(tags, "UserId")) then
                        return data
                    end
                    if not tags and not fallback and InventoryLooksValid(inv) then
                        fallback = data
                    end
                end
            end
            
            local inv = rawget(obj, "Inventory")
            if not fallback and InventoryLooksValid(inv) then
                fallback = obj
            end
        end
    end
    return fallback
end

local function GetPlayerDataViaGC()
    if type(getgc) ~= "function" then return nil end
    local ok, objects = pcall(getgc, true)
    if not ok or type(objects) ~= "table" then return nil end
    return FindPlayerDataInObjects(objects)
end

local function GetPlayerDataViaRegistry()
    if type(debug) ~= "table" or type(debug.getregistry) ~= "function" then return nil end
    local ok, registry = pcall(debug.getregistry)
    if not ok or type(registry) ~= "table" then return nil end
    return FindPlayerDataInObjects(registry)
end

local function GetPlayerDataViaReplicaClient()
    local replicaClient = ReplicatedStorage:FindFirstChild("ReplicaClient")
    if not replicaClient then return nil end
    
    local ok, module = pcall(require, replicaClient)
    if not ok or type(module) ~= "table" then
        return nil
    end
    
    local userId = LocalPlayer and LocalPlayer.UserId
    if not userId then return nil end
    
    local replicaSources = {module.Replicas, module._replicas, module.replicas}
    for _, replicas in pairs(replicaSources) do
        if type(replicas) == "table" then
            for _, replica in pairs(replicas) do
                if type(replica) == "table" then
                    local tags = rawget(replica, "Tags")
                    local data = rawget(replica, "Data")
                    if type(tags) == "table" and type(data) == "table" then
                        local objUserId = rawget(tags, "UserId")
                        if objUserId == userId or tonumber(objUserId) == userId then
                            if type(rawget(data, "Inventory")) == "table" then
                                return data
                            end
                        end
                    end
                end
            end
        end
    end
    
    return nil
end

local function GetPlayerData()
    local data = GetPlayerDataViaGC()
    if data then return data, "gc" end
    
    data = GetPlayerDataViaRegistry()
    if data then return data, "registry" end
    
    data = GetPlayerDataViaReplicaClient()
    if data then return data, "replica" end
    
    return nil, nil
end

-- Find PlayerStatus (contains Movement data with DashCooldown)
local function GetPlayerStatus()
    if type(getgc) ~= "function" then return nil end
    local ok, objects = pcall(getgc, true)
    if not ok or type(objects) ~= "table" then return nil end
    
    local userId = LocalPlayer and LocalPlayer.UserId
    if not userId then return nil end
    
    for _, obj in pairs(objects) do
        if type(obj) == "table" then
            local token = rawget(obj, "Token")
            local tags = rawget(obj, "Tags")
            local data = rawget(obj, "Data")
            
            -- Look for PlayerStatus token
            if token == "PlayerStatus" and type(data) == "table" then
                -- Verify it's for our player
                if type(tags) == "table" then
                    local objUserId = rawget(tags, "UserId")
                    if objUserId == userId or tonumber(objUserId) == userId then
                        return data
                    end
                else
                    -- If no tags, check for Movement table
                    if type(rawget(data, "Movement")) == "table" then
                        return data
                    end
                end
            end
        end
    end
    
    return nil
end

-- ═══════════════════════════════════════════════════════════════════════════
-- NPC TELEPORT POSITION
-- ═══════════════════════════════════════════════════════════════════════════

local function GetNPCTeleportPosition()
    local proximity = Workspace:FindFirstChild("Proximity")
    local npc = proximity and proximity:FindFirstChild("Greedy Cey")
    if not npc then return nil end
    
    local cframe
    if npc:IsA("Model") then
        local part = npc.PrimaryPart or npc:FindFirstChild("HumanoidRootPart")
        cframe = part and part.CFrame or npc:GetPivot()
    elseif npc:IsA("BasePart") then
        cframe = npc.CFrame
    end
    
    if cframe then
        return cframe.Position + cframe.LookVector * 5
    end
    return nil
end

-- ═══════════════════════════════════════════════════════════════════════════
-- BASKET BUILDING
-- ═══════════════════════════════════════════════════════════════════════════

local function GetFavorites(data)
    local favorites = {}
    if data and type(data.Favorites) == "table" then
        for key, _ in pairs(data.Favorites) do
            favorites[key] = true
        end
    end
    return favorites
end

local function IsGUID(str)
    if type(str) ~= "string" then return false end
    return str:match("^%x%x%x%x%x%x%x%x%-%x%x%x%x%-%x%x%x%x%-%x%x%x%x%-%x%x%x%x%x%x%x%x%x%x%x%x$") ~= nil
end

local function BuildBasket()
    local data, method = GetPlayerData()
    if not data then
        return nil, "player data not found (no method worked)"
    end
    
    Log("Player data found via: " .. method)
    
    local inventory = data.Inventory
    if not inventory then
        return nil, "inventory not found in player data"
    end
    
    local favorites = GetFavorites(data)
    local basket = {}
    local itemCount = 0
    
    -- Add ores from inventory
    for name, count in pairs(inventory) do
        if type(name) == "string" and type(count) == "number" and count > 0 then
            if not DoNotSell[name] and not EssenceNames[name] then
                if not IsGUID(name) then
                    if not Config.SkipFavorites or not favorites[name] then
                        basket[name] = count
                        itemCount = itemCount + count
                    end
                end
            end
        end
    end
    
    -- Add essences from Misc
    local misc = inventory.Misc
    if type(misc) == "table" then
        for _, item in pairs(misc) do
            if type(item) == "table" then
                local name = item.Name
                local quantity = item.Quantity
                local guid = item.GUID
                local addedToBasket = false
                
                -- Check for essence items (have Name and Quantity)
                if name and quantity and type(quantity) == "number" and quantity > 0 then
                    if EssenceNames[name] then
                        if not Config.SkipFavorites or not favorites[name] then
                            basket[name] = (basket[name] or 0) + quantity
                            itemCount = itemCount + quantity
                            addedToBasket = true
                        end
                    end
                end
                
                -- Check for GUID items (runes, misc items) - if not already added as essence
                if not addedToBasket and guid then
                    local isEquipment = item.Ores or item.Runes or item.Upgrade or item.Type
                    -- Rune items (with Traits) are now sellable, protected by favorites
                    
                    if not isEquipment then
                        if not Config.SkipFavorites or not favorites[guid] then
                            basket[guid] = 1
                            itemCount = itemCount + 1
                        end
                    end
                end
            end
        end
    end
    
    if next(basket) == nil then
        return nil, "no sellable items found"
    end
    
    return basket, nil, itemCount
end

-- ═══════════════════════════════════════════════════════════════════════════
-- FLY SYSTEM
-- ═══════════════════════════════════════════════════════════════════════════

local function GetCharacter()
    local living = Workspace:FindFirstChild("Living")
    if living then
        return living:FindFirstChild(LocalPlayer.Name)
    end
    return LocalPlayer.Character
end

local function GetRoot(char)
    return char and char:FindFirstChild("HumanoidRootPart")
end

local function CreateMagicCarpet()
    if MagicCarpet then return end
    MagicCarpet = Instance.new("Part")
    MagicCarpet.Name = "SellModuleCarpet"
    MagicCarpet.Size = Vector3.new(6, 0.5, 6)
    MagicCarpet.Transparency = 1
    MagicCarpet.Anchored = true
    MagicCarpet.CanCollide = false
    MagicCarpet.Parent = Workspace
end

local function UpdateMagicCarpet(rootPart)
    if not MagicCarpet or not rootPart or not rootPart.Parent then return end
    MagicCarpet.CFrame = rootPart.CFrame * CFrame.new(0, CARPET_OFFSET, 0)
end

local function DestroyMagicCarpet()
    if MagicCarpet then
        MagicCarpet:Destroy()
        MagicCarpet = nil
    end
end

local function StopFlying()
    IsFlying = false
    
    if FlyConnection then
        FlyConnection:Disconnect()
        FlyConnection = nil
    end
    
    if NoClipConnection then
        NoClipConnection:Disconnect()
        NoClipConnection = nil
    end
    
    local char = GetCharacter()
    if char then
        local root = GetRoot(char)
        local hum = char:FindFirstChild("Humanoid")
        
        if root then
            root.AssemblyLinearVelocity = Vector3.zero
            root.AssemblyAngularVelocity = Vector3.zero
        end
        
        if hum and hum.PlatformStand then
            hum.PlatformStand = false
        end
        
        for _, part in pairs(char:GetDescendants()) do
            if part:IsA("BasePart") then part.CanCollide = true end
        end
    end
    
    if BodyGyro then
        BodyGyro:Destroy()
        BodyGyro = nil
    end
    
    if char then
        local root = GetRoot(char)
        if root then
            local bodyPos = root:FindFirstChild("SellBodyPosition")
            if bodyPos then bodyPos:Destroy() end
        end
    end
    
    DestroyMagicCarpet()
end

local function FlyTo(targetPos, targetName)
    if IsFlying then
        StopFlying()
        task.wait(0.1)
    end
    
    local char = GetCharacter()
    local root = GetRoot(char)
    local hum = char and char:FindFirstChild("Humanoid")
    
    if not root or not hum then
        Log("FlyTo failed: Character not found")
        return
    end
    
    hum.PlatformStand = true
    root.AssemblyLinearVelocity = Vector3.zero
    root.AssemblyAngularVelocity = Vector3.zero
    
    for _, part in pairs(char:GetDescendants()) do
        if part:IsA("BasePart") then
            part.CanCollide = false
        end
    end
    
    IsFlying = true
    CreateMagicCarpet()
    UpdateMagicCarpet(root)
    
    Log("Flying to: " .. (targetName or "NPC"))
    
    NoClipConnection = RunService.Heartbeat:Connect(function()
        if not IsFlying then return end
        local char = GetCharacter()
        if not char then return end
        
        for _, part in pairs(char:GetDescendants()) do
            if part:IsA("BasePart") and part.CanCollide then
                part.CanCollide = false
            end
        end
    end)
    
    FlyConnection = RunService.Heartbeat:Connect(function(deltaTime)
        if not IsFlying then return end
        
        local char = GetCharacter()
        local root = GetRoot(char)
        local hum = char and char:FindFirstChild("Humanoid")
        
        if not root or not hum then return end
        
        UpdateMagicCarpet(root)
        
        if not hum.PlatformStand then hum.PlatformStand = true end
        
        local currentPos = root.Position
        local diff = targetPos - currentPos
        local distance = diff.Magnitude
        
        if distance < STOP_DISTANCE then
            Log("Arrived at destination")
            StopFlying()
            return
        end
        
        local moveSpeed = FLY_SPEED * (deltaTime or 1/60)
        local direction = diff.Unit
        local moveDistance = math.min(moveSpeed, distance)
        local newPos = currentPos + direction * moveDistance
        
        if not BodyGyro then
            BodyGyro = Instance.new("BodyGyro")
            BodyGyro.MaxTorque = Vector3.new(1e9, 1e9, 1e9)
            BodyGyro.P = 10000
            BodyGyro.D = 100
            BodyGyro.Parent = root
        end
        
        local flatLook = Vector3.new(targetPos.X, newPos.Y, targetPos.Z)
        local lookDist = (flatLook - newPos).Magnitude
        if lookDist > 0.1 then
            BodyGyro.CFrame = CFrame.lookAt(newPos, flatLook)
        end
        
        local bodyPos = root:FindFirstChild("SellBodyPosition")
        if not bodyPos then
            bodyPos = Instance.new("BodyPosition")
            bodyPos.Name = "SellBodyPosition"
            bodyPos.MaxForce = Vector3.new(1e6, 1e6, 1e6)
            bodyPos.P = 50000
            bodyPos.D = 1000
            bodyPos.Parent = root
        end
        bodyPos.Position = newPos
        
        root.CFrame = CFrame.new(newPos)
        root.AssemblyLinearVelocity = Vector3.zero
        root.AssemblyAngularVelocity = Vector3.zero
    end)
end

-- ═══════════════════════════════════════════════════════════════════════════
-- SELL LOGIC (Instant Teleport Pattern - like region_bypass reversed)
-- First sell teleports to NPC, subsequent sells skip teleport
-- ═══════════════════════════════════════════════════════════════════════════

local function OpenSellDialogue(remotes, npc)
    if not remotes or not remotes.ForceDialogue or not remotes.Dialogue or not npc then
        return false
    end
    
    -- Step 1: request initial dialogue prompt (SellDialogueMisc). If it succeeds, simulate Yes; otherwise continue.
    local ok, result = pcall(function()
        return remotes.Dialogue:InvokeServer(npc)
    end)
    if ok and result ~= false then
        local gotPrompt = WaitForDialogueRoot("SellDialogueMisc", 1.5)
        if gotPrompt and remotes.DialogueEvent then
            pcall(function() remotes.DialogueEvent:FireServer("Opened") end)
            pcall(function() remotes.DialogueEvent:FireServer("Closed") end)
        end
    end
    
    -- Step 2: open sell confirm (ForceDialogue) with retry if needed
    local okForce = false
    ok, result = pcall(function()
        return remotes.ForceDialogue:InvokeServer(npc, "SellConfirmMisc")
    end)
    if ok and result ~= false then
        okForce = true
    end
    if not okForce then
        task.wait(0.5)
        local ok2, res2 = pcall(function()
            return remotes.ForceDialogue:InvokeServer(npc, "SellConfirmMisc")
        end)
        if ok2 and res2 ~= false then
            okForce = true
        end
    end
    -- Treat a successful pcall (even if result is nil) as success; only explicit false fails
    if not okForce and ok and result == nil then okForce = true end
    if not okForce then
        return false
    end
    
    -- Step 3: wait for server to send SellConfirmMisc root before we RunCommand (retry once); do not fail hard if missing
    local gotConfirm, confirmCtx = WaitForDialogueRoot("SellConfirmMisc", 2)
    if not gotConfirm then
        task.wait(0.5)
        gotConfirm, confirmCtx = WaitForDialogueRoot("SellConfirmMisc", 2)
    end
    if not gotConfirm then
        Log("Warning: SellConfirmMisc not observed, continuing anyway")
    end
    if confirmCtx then
        CachedConfirmCtx = confirmCtx
        CachedConfirmTime = os.clock()
    end
    -- Step 4: mark opened once for confirm dialog
    if remotes.DialogueEvent then
        pcall(function() remotes.DialogueEvent:FireServer("Opened") end)
    end
    
    return true
end

local function CloseSellDialogue(remotes)
    if not remotes then return end
    
    -- STEP 1: Remove DisableBackpack tag from Character.Status
    -- This is what actually locks movement (discovered from DialogueHandler decompile)
    local char = GetCharacter()
    if char then
        local status = char:FindFirstChild("Status")
        if status then
            local disableBackpack = status:FindFirstChild("DisableBackpack")
            if disableBackpack then
                Log("Removing DisableBackpack tag from Status")
                pcall(function() disableBackpack:Destroy() end)
            end
        end
    end
    
    -- STEP 2: Fire close event to server
    if remotes.DialogueEvent then
        pcall(function() remotes.DialogueEvent:FireServer("Closed") end)
    end

    pcall(function()
        GuiService.SelectedObject = nil
        if GuiService.ClearSelection then
            GuiService:ClearSelection()
        end
    end)
    
    -- STEP 3: Clean up DialogueUI visuals (avoid toggling Enabled to prevent stale state)
    local playerGui = LocalPlayer:FindFirstChild("PlayerGui")
    if playerGui then
        local dialogueUI = playerGui:FindFirstChild("DialogueUI")
        if dialogueUI then
            -- Hide all GuiButtons to prevent InputAction.IsActive() from blocking dash
            for _, descendant in pairs(dialogueUI:GetDescendants()) do
                if descendant:IsA("GuiButton") then
                    pcall(function() 
                        descendant.Visible = false 
                        descendant.Interactable = false
                    end)
                end
            end
        end
        
        -- Also hide ResponseBillboard if it exists
        local responseBillboard = dialogueUI and dialogueUI:FindFirstChild("ResponseBillboard")
        if responseBillboard then
            pcall(function() responseBillboard.Visible = false end)
        end
    end
end

local function SellOnce(opts)
    if IsSelling then return end
    IsSelling = true
    
    -- Temporarily disable DialogueHandler to avoid client errors; we'll manage closure ourselves
    ToggleDialogueHandler(true)

    local basket, reason, count = BuildBasket()
    if not basket then
        IsSelling = false
        Notify("Auto Sell", reason or "No items", 2)
        ToggleDialogueHandler(false)
        return
    end
    
    Log("Basket built with " .. count .. " items")
    
    local remotes = GetRemotes()
    if not remotes.RunCommand or not remotes.ForceDialogue or not remotes.Dialogue then
        IsSelling = false
        Notify("Auto Sell", "Remotes not found", 3)
        ToggleDialogueHandler(false)
        return
    end
    
    -- Get NPC (needed for ForceDialogue)
    local npc = GetNPC()
    if not npc then
        IsSelling = false
        Notify("Auto Sell", "NPC Greedy Cey not found", 3)
        ToggleDialogueHandler(false)
        return
    end
    
    local char = GetCharacter()
    local root = GetRoot(char)
    local hum = char and char:FindFirstChild("Humanoid")
    local originalCFrame = root and root.CFrame
    local didTeleport = false
    
    -- Save WalkSpeed/JumpPower before dialog (dialog controller sets them to 0)
    local savedWalkSpeed = hum and hum.WalkSpeed or 16
    local savedJumpPower = hum and hum.JumpPower or 50
    
    local forceTeleport = opts and opts.forceTeleport
    local noTeleport = opts and opts.noTeleport
    Log("SellOnce called: noTeleport=" .. tostring(noTeleport) .. ", forceTeleport=" .. tostring(forceTeleport))
    if forceTeleport then
        HasInitializedSell = false -- paksa jalur teleport
    end

    local dialogOpened = false
    -- Try reuse cached context first (for no-teleport mode)
    dialogOpened = TryReuseCachedConfirm(remotes)
    if dialogOpened then
        Log("Using cached context - skipping OpenSellDialogue")
    else
        Log("Opening dialogue...")
        dialogOpened = OpenSellDialogue(remotes, npc)
    end



    -- Jika gagal dan user minta noTeleport atau sudah pernah init dengan NoTeleportAfterFirst, berhenti tanpa teleport
    Log("dialogOpened=" .. tostring(dialogOpened) .. ", noTeleport=" .. tostring(noTeleport) .. ", HasInitializedSell=" .. tostring(HasInitializedSell))
    if not dialogOpened and (noTeleport or (HasInitializedSell and Config.NoTeleportAfterFirst)) then
        Log("Returning early - dialog not opened and noTeleport mode")
        IsSelling = false
        Notify("Auto Sell", "Dialog tidak dapat dibuka tanpa teleport. Dekati NPC.", 3)
        ToggleDialogueHandler(false)
        return
    end
    
    -- Jika masih gagal, baru paksa teleport (kecuali noTeleport)
    if not dialogOpened and not noTeleport then
        local npcPos = GetNPCTeleportPosition()
        if not npcPos then
            IsSelling = false
            Notify("Auto Sell", "NPC position not found", 3)
            ToggleDialogueHandler(false)
            return
        end
        
        if not root then
            IsSelling = false
            Notify("Auto Sell", "Character not found", 3)
            ToggleDialogueHandler(false)
            return
        end
        
        Log("Teleporting to Greedy Cey...")
        didTeleport = true
        root.CFrame = CFrame.new(npcPos)
        root.AssemblyLinearVelocity = Vector3.zero
        root.AssemblyAngularVelocity = Vector3.zero
        task.wait(0.1)
        
        Log("Opening dialogue...")
        dialogOpened = OpenSellDialogue(remotes, npc)
    end
    
    if not dialogOpened then
        if didTeleport and originalCFrame and root then
            root.CFrame = originalCFrame
            root.AssemblyLinearVelocity = Vector3.zero
            root.AssemblyAngularVelocity = Vector3.zero
        end
        HasInitializedSell = false
        IsSelling = false
        Notify("Auto Sell", "Failed to open dialogue", 3)
        ToggleDialogueHandler(false)
        return
    end
    
    HasInitializedSell = true
    
    -- Sell
    Log("Sending SellConfirm with basket...")
    local sellSuccess = false
    local ok, result = pcall(function()
        return remotes.RunCommand:InvokeServer("SellConfirm", {Basket = basket})
    end)
    if ok and result ~= false then
        sellSuccess = true
    end
    task.wait(0.1)
    
    Log("Closing dialogue...")
    CloseSellDialogue(remotes)
    
    ToggleDialogueHandler(false)

    -- TRIGGER AUTO-CLOSE BY RANGE (skip for noTeleport mode)
    -- DialogueHandler auto-closes when player is >18 units from NPC
    -- Teleport far away briefly, wait for range check (runs every 1s), then return
    if not noTeleport and root and npc then
        local npcPos = npc.HumanoidRootPart and npc.HumanoidRootPart.Position or npc.PrimaryPart and npc.PrimaryPart.Position
        if npcPos then
            local farAwayPos = npcPos + Vector3.new(50, 0, 50) -- 50+ units away
            Log("Teleporting away to trigger dialogue auto-close...")
            root.CFrame = CFrame.new(farAwayPos)
            root.AssemblyLinearVelocity = Vector3.zero
            root.AssemblyAngularVelocity = Vector3.zero
            task.wait(1.2) -- Wait for range check (runs every 1 second)
        end
    end
    
    if didTeleport and originalCFrame and root then
        Log("Returning to original position...")
        root.CFrame = originalCFrame
        root.AssemblyLinearVelocity = Vector3.zero
        root.AssemblyAngularVelocity = Vector3.zero
        task.wait(0.1)
    end
    
    if sellSuccess then
        LastSellTime = tick()
        Notify("Auto Sell", string.format("Sold %d items", count), 2)
        Log("Sell SUCCESS!")
    else
        Notify("Auto Sell", "Sell failed", 3)
        Log("Sell FAILED")
    end
    
    IsSelling = false
    
    -- COMPREHENSIVE MOVEMENT RESTORATION
    local char = GetCharacter()
    local hum = char and char:FindFirstChild("Humanoid")
    local root = char and char:FindFirstChild("HumanoidRootPart")
    
    if hum then
        -- Remove blocking tags in Status (BoolValues AND check NumberValues)
        local status = char:FindFirstChild("Status")
        if status then
            for _, child in pairs(status:GetChildren()) do
                -- Remove blocking BoolValues
                if child:IsA("BoolValue") and ShouldClearStatusBool(child.Name) then
                    Log("Removing Status BoolValue: " .. child.Name)
                    pcall(function() child:Destroy() end)
                end
                
                -- Check for dash-blocking NumberValues
                if child:IsA("NumberValue") and child.Name:lower():find("dashcooldown") then
                    Log("Resetting dash cooldown NumberValue: " .. child.Name .. " = " .. tostring(child.Value))
                    pcall(function() child.Value = 0 end)
                end
            end
        end
        
        -- Fix all possible blocking states
        hum.PlatformStand = false
        hum.Sit = false
        
        -- Restore movement speeds
        if hum.WalkSpeed == 0 or hum.WalkSpeed < savedWalkSpeed then
            hum.WalkSpeed = savedWalkSpeed
            Log("WalkSpeed restored to " .. savedWalkSpeed)
        end
        if hum.JumpPower == 0 or hum.JumpPower < savedJumpPower then
            hum.JumpPower = savedJumpPower
            Log("JumpPower restored to " .. savedJumpPower)
        end
        
        -- Unanchor root part
        if root and root.Anchored then
            root.Anchored = false
            Log("HumanoidRootPart unanchored")
        end
        
        -- Force humanoid state to Running
        pcall(function() hum:ChangeState(Enum.HumanoidStateType.Running) end)
        
        -- Reset PlayerStatus Movement data (DashCooldown, etc)
        pcall(function()
            local playerStatus = GetPlayerStatus()
            if playerStatus and playerStatus.Movement then
                if ResetDashState(playerStatus.Movement) then
                    Log("Reset dash cooldown via PlayerStatus")
                end
            end
        end)
        
        -- Try to reset dash via Knit controller (PlayerController.Status.Data.Movement)
        pcall(function()
            local Shared = ReplicatedStorage:FindFirstChild("Shared")
            local Packages = Shared and Shared:FindFirstChild("Packages")
            local Knit = Packages and Packages:FindFirstChild("Knit")
            if Knit then
                local KnitModule = require(Knit)
                if KnitModule.GetController then
                    -- PlayerController has Status with Data.Movement
                    local PlayerController = KnitModule.GetController("PlayerController")
                    if PlayerController and PlayerController.Status then
                        local status = PlayerController.Status
                        if status.Data and status.Data.Movement then
                            if ResetDashState(status.Data.Movement) then
                                Log("Reset PlayerController.Status.Data.Movement.DashCooldown")
                            end
                        end
                    end
                    
                    -- Also check CharacterController
                    local CharacterController = KnitModule.GetController("CharacterController")
                    if CharacterController then
                        if CharacterController.Cooldowns then
                            CharacterController.Cooldowns.StaminaInterfaceCd = 0
                        end
                    end
                end
            end
        end)
        
        -- Try to unlock InputAction system
        pcall(function()
            local InputAction = require(ReplicatedStorage.Shared.InputAction)
            if InputAction then
                -- Try various unlock methods
                if InputAction.Unlock then
                    InputAction:Unlock(Enum.KeyCode.Q)
                    Log("Unlocked Q key via InputAction")
                end
                if InputAction.UnlockAll then
                    InputAction:UnlockAll()
                end
                if InputAction.Clear then
                    InputAction:Clear()
                end
            end
        end)
        
        -- One more comprehensive restore after delay
        task.delay(0.5, function()
            if hum then
                hum.PlatformStand = false
                hum.Sit = false
                if hum.WalkSpeed == 0 then hum.WalkSpeed = savedWalkSpeed end
                if hum.JumpPower == 0 then hum.JumpPower = savedJumpPower end
                pcall(function() hum:ChangeState(Enum.HumanoidStateType.Running) end)
            end
            if root and root.Anchored then root.Anchored = false end
            
            -- Clean up any remaining blocking tags
            local char = GetCharacter()
            local status = char and char:FindFirstChild("Status")
            if status then
                for _, child in pairs(status:GetChildren()) do
                    if child:IsA("BoolValue") and ShouldClearStatusBool(child.Name) then
                        pcall(function() child:Destroy() end)
                    end
                end
            end
        end)
    end
end
-- AUTO SELL LOOP
-- ═══════════════════════════════════════════════════════════════════════════

local function StartAutoSell()
    if AutoSellThread then return end
    AutoSellThread = task.spawn(function()
        while Config.AutoSell do
            task.wait(0.5)
            if not Config.AutoSell then break end
            if not IsSelling and (tick() - LastSellTime) >= Config.SellInterval then
                SellOnce()
            end
        end
        AutoSellThread = nil
    end)
end

local function StopAutoSell()
    Config.AutoSell = false
end

-- ═══════════════════════════════════════════════════════════════════════════
-- RESET FUNCTION
-- ═══════════════════════════════════════════════════════════════════════════

Forge.ResetSell = function()
    Config.AutoSell = false
    IsSelling = false
    HasInitializedSell = false
    LastSellTime = 0
    for k, v in pairs(DefaultConfig) do
        Config[k] = v
    end
    local playerUI = _G.Forge.PlayerUIElements
    if playerUI then
        if playerUI.AutoSellToggle then
            pcall(function() playerUI.AutoSellToggle:Set(false) end)
        end
        if playerUI.SellIntervalSlider then
            pcall(function() playerUI.SellIntervalSlider:Set(DefaultConfig.SellInterval) end)
        end
        if playerUI.SkipFavoritesToggle then
            pcall(function() playerUI.SkipFavoritesToggle:Set(DefaultConfig.SkipFavorites) end)
        end
    end
    Log("Config reset to defaults")
end

-- ═══════════════════════════════════════════════════════════════════════════
-- EXPOSE FUNCTIONS VIA _G.Forge
-- ═══════════════════════════════════════════════════════════════════════════

Forge.SellOnce = SellOnce
Forge.SellOnceNoTeleport = function()
    return SellOnce({ noTeleport = true })
end
Forge.SellOnceForceTeleport = function()
    return SellOnce({ forceTeleport = true })
end
Forge.StartAutoSell = StartAutoSell
Forge.StopAutoSell = StopAutoSell
Forge.GetSellPlayerData = GetPlayerData

-- ═══════════════════════════════════════════════════════════════════════════
-- CLEANUP
-- ═══════════════════════════════════════════════════════════════════════════

local function Cleanup()
    StopAutoSell()
    StopFlying()
    Log("Cleanup complete")
end

table.insert(Forge.Cleanup, Cleanup)

-- ═══════════════════════════════════════════════════════════════════════════
-- INIT
-- ═══════════════════════════════════════════════════════════════════════════

Log("Module v1.0 loaded!")
Rayfield:Notify({Title = "Sell Module", Content = "v1.0 Loaded!", Duration = 2})
