local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 87) then
					if (Enum <= 43) then
						if (Enum <= 21) then
							if (Enum <= 10) then
								if (Enum <= 4) then
									if (Enum <= 1) then
										if (Enum > 0) then
											Upvalues[Inst[3]] = Stk[Inst[2]];
										else
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum <= 2) then
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 3) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 7) then
									if (Enum <= 5) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 6) then
										local B;
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 8) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 9) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 15) then
								if (Enum <= 12) then
									if (Enum > 11) then
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 13) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 14) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 18) then
								if (Enum <= 16) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 17) then
									Stk[Inst[2]] = {};
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 19) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Enum == 20) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 32) then
							if (Enum <= 26) then
								if (Enum <= 23) then
									if (Enum == 22) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]]();
									end
								elseif (Enum <= 24) then
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum == 25) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 29) then
								if (Enum <= 27) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 28) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 30) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
							elseif (Enum == 31) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 37) then
							if (Enum <= 34) then
								if (Enum > 33) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 35) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 36) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 40) then
							if (Enum <= 38) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							elseif (Enum == 39) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 41) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum == 42) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 65) then
						if (Enum <= 54) then
							if (Enum <= 48) then
								if (Enum <= 45) then
									if (Enum > 44) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 46) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								elseif (Enum > 47) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 51) then
								if (Enum <= 49) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 50) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 52) then
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 53) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 59) then
							if (Enum <= 56) then
								if (Enum == 55) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Results = {Stk[A]()};
									local Limit = Inst[4];
									local Edx = 0;
									for Idx = A, Limit do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 57) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Enum == 58) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 62) then
							if (Enum <= 60) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 61) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 63) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum > 64) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 76) then
						if (Enum <= 70) then
							if (Enum <= 67) then
								if (Enum == 66) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								end
							elseif (Enum <= 68) then
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum == 69) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 73) then
							if (Enum <= 71) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 72) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 74) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 75) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 81) then
						if (Enum <= 78) then
							if (Enum > 77) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 79) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum > 80) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 84) then
						if (Enum <= 82) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						elseif (Enum > 83) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 85) then
						local A = Inst[2];
						local Cls = {};
						for Idx = 1, #Lupvals do
							local List = Lupvals[Idx];
							for Idz = 0, #List do
								local Upv = List[Idz];
								local NStk = Upv[1];
								local DIP = Upv[2];
								if ((NStk == Stk) and (DIP >= A)) then
									Cls[DIP] = NStk[DIP];
									Upv[1] = Cls;
								end
							end
						end
					elseif (Enum == 86) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 131) then
					if (Enum <= 109) then
						if (Enum <= 98) then
							if (Enum <= 92) then
								if (Enum <= 89) then
									if (Enum == 88) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 90) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 91) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 95) then
								if (Enum <= 93) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 94) then
									local A = Inst[2];
									do
										return Stk[A], Stk[A + 1];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 96) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Enum == 97) then
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 103) then
							if (Enum <= 100) then
								if (Enum > 99) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 101) then
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 102) then
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 106) then
							if (Enum <= 104) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 105) then
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 107) then
							VIP = Inst[3];
						elseif (Enum > 108) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 120) then
						if (Enum <= 114) then
							if (Enum <= 111) then
								if (Enum > 110) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 112) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 113) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 117) then
							if (Enum <= 115) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 116) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 118) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 119) then
							Stk[Inst[2]] = Inst[3];
						else
							local Edx;
							local Limit;
							local Results;
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A]()};
							Limit = Inst[4];
							Edx = 0;
							for Idx = A, Limit do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 125) then
						if (Enum <= 122) then
							if (Enum == 121) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 123) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 124) then
							local B;
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 128) then
						if (Enum <= 126) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						elseif (Enum > 127) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 129) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 130) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 153) then
					if (Enum <= 142) then
						if (Enum <= 136) then
							if (Enum <= 133) then
								if (Enum > 132) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 134) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							elseif (Enum > 135) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 139) then
							if (Enum <= 137) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 138) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 140) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 141) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 147) then
						if (Enum <= 144) then
							if (Enum == 143) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 145) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum > 146) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 150) then
						if (Enum <= 148) then
							local A;
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						elseif (Enum == 149) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 151) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Enum > 152) then
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					else
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 164) then
					if (Enum <= 158) then
						if (Enum <= 155) then
							if (Enum == 154) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 156) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Enum == 157) then
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 161) then
						if (Enum <= 159) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 160) then
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 162) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 163) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						local B;
						local A;
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 169) then
					if (Enum <= 166) then
						if (Enum > 165) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 167) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum > 168) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 172) then
					if (Enum <= 170) then
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum == 171) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					end
				elseif (Enum <= 173) then
					Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
				elseif (Enum == 174) then
					local NewProto = Proto[Inst[3]];
					local NewUvals;
					local Indexes = {};
					NewUvals = Setmetatable({}, {__index=function(_, Key)
						local Val = Indexes[Key];
						return Val[1][Val[2]];
					end,__newindex=function(_, Key, Value)
						local Val = Indexes[Key];
						Val[1][Val[2]] = Value;
					end});
					for Idx = 1, Inst[4] do
						VIP = VIP + 1;
						local Mvm = Instr[VIP];
						if (Mvm[1] == 168) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				else
					local B;
					local A;
					Upvalues[Inst[3]] = Stk[Inst[2]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A] = Stk[A]();
					VIP = VIP + 1;
					Inst = Instr[VIP];
					B = Stk[Inst[4]];
					if B then
						VIP = VIP + 1;
					else
						Stk[Inst[2]] = B;
						VIP = Inst[3];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!493Q0003023Q006F7303053Q00636C6F636B03043Q007461736B03043Q0077616974026Q00E03F03023Q005F4703053Q00466F72676503043Q005461627303063Q00506C6179657203083Q005261796669656C64026Q00244003043Q007761726E032C3Q005B53652Q6C5D20446570656E64656E63696573206E6F742072656164793B2061626F7274696E67206C6F616403043Q0067616D65030A3Q004765745365727669636503073Q00506C617965727303113Q005265706C69636174656453746F72616765030A3Q0052756E53657276696365030A3Q004775695365727669636503093Q00576F726B7370616365030B3Q004C6F63616C506C6179657203083Q004175746F53652Q6C0100030C3Q0053652Q6C496E74657276616C026Q003E40030C3Q0053652Q6C432Q6F6C646F776E027Q0040030D3Q00536B69704661766F72697465732Q0103143Q004E6F54656C65706F72744166746572466972737403053Q007061697273030A3Q0053652Q6C436F6E66696703113Q0053652Q6C44656661756C74436F6E666967028Q00030E3Q00436861726163746572412Q64656403073Q00436F2Q6E656374026Q003440026Q000CC0026Q002040030C3Q0054696E7920452Q73656E6365030D3Q00536D612Q6C20452Q73656E6365030E3Q004D656469756D20452Q73656E6365030D3Q004C6172676520452Q73656E6365030F3Q004772656174657220452Q73656E636503103Q005375706572696F7220452Q73656E6365030C3Q004570696320452Q73656E636503113Q004C6567656E6461727920452Q73656E6365030D3Q0053696D706C654C616E7465726E030A3Q00506F7274616C542Q6F6C03163Q004368726973746D61734576656E7443752Q72656E637903043Q004D697363030A3Q0045717569706D656E747303043Q00722Q6F74002Q033Q0063747803043Q0074696D6503093Q00526573657453652Q6C03083Q0053652Q6C4F6E636503123Q0053652Q6C4F6E63654E6F54656C65706F727403153Q0053652Q6C4F6E6365466F72636554656C65706F7274030D3Q0053746172744175746F53652Q6C030C3Q0053746F704175746F53652Q6C03113Q0047657453652Q6C506C617965724461746103053Q007461626C6503063Q00696E7365727403073Q00436C65616E757003133Q004D6F64756C652076312E30206C6F616465642103063Q004E6F7469667903053Q005469746C65030B3Q0053652Q6C204D6F64756C6503073Q00436F6E74656E74030C3Q0076312E30204C6F616465642103083Q004475726174696F6E002F012Q00120A3Q00013Q0020965Q00022Q00973Q0001000200120A000100033Q002Q2000010001000400122Q000200056Q00010002000100122Q000100063Q00202Q00010001000700062Q0001001B00013Q00046B3Q001B000100120A000100063Q0020960001000100070020960001000100080006280001001B00013Q00046B3Q001B000100120A000100063Q0020960001000100070020960001000100080020960001000100090006280001001B00013Q00046B3Q001B000100120A000100063Q00209600010001000700209600010001000A00060F000100210001000100046B3Q0021000100120A000100013Q0020960001000100022Q00970001000100022Q0026000100013Q000E88000B00030001000100046B3Q0003000100120A000100063Q0020960001000100070006280001003500013Q00046B3Q0035000100120A000100063Q0020960001000100070020960001000100080006280001003500013Q00046B3Q0035000100120A000100063Q0020960001000100070020960001000100080020960001000100090006280001003500013Q00046B3Q0035000100120A000100063Q00209600010001000700209600010001000A00060F000100390001000100046B3Q0039000100120A0001000C3Q0012780002000D4Q00350001000200012Q00663Q00013Q00120A0001000E3Q00201100010001000F00122Q000300106Q00010003000200122Q0002000E3Q00202Q00020002000F00122Q000400116Q00020004000200122Q0003000E3Q00202Q00030003000F00122Q000500124Q00190003000500020012590004000E3Q00202Q00040004000F00122Q000600136Q00040006000200122Q0005000E3Q00202Q00050005000F00122Q000700146Q00050007000200202Q00060001001500122Q000700063Q00209600070007000700207D00080007000A4Q00093Q000500302Q00090016001700302Q00090018001900302Q0009001A001B00302Q0009001C001D00302Q0009001E001D4Q000A5Q00122Q000B001F6Q000C00094Q0018000B0002000D00046B3Q005D00012Q0039000A000E000F00065C000B005C0001000200046B3Q005C00010010A400070020000A0010830007002100094Q000B000B3Q00122Q000C00226Q000D8Q000E5Q00062Q0006006C00013Q00046B3Q006C0001002096000F00060023002023000F000F00240006AE00113Q000100012Q00A83Q000E4Q0073000F001100012Q0009000F00124Q005E00135Q00122Q001400253Q00122Q001500263Q00122Q001600276Q00173Q000800302Q00170028001D00302Q00170029001D00302Q0017002A001D00302Q0017002B001D00302Q0017002C001D00309B0017002D001D0030130017002E001D00302Q0017002F001D4Q00183Q000500302Q00180030001D00302Q00180031001D00302Q00180032001D00302Q00180033001D00302Q00180034001D000242001900013Q0006AE001A0002000100012Q00A83Q00083Q000242001B00033Q0006AE001C0004000100012Q00A83Q001B3Q000242001D00054Q000C001E3Q000300302Q001E0035003600302Q001E0037003600302Q001E003800224Q001F00203Q00122Q002100223Q0006AE00220006000100052Q00A83Q001F4Q00A83Q00024Q00A83Q001E4Q00A83Q00204Q00A83Q00213Q0006AE00230007000100032Q00A83Q00224Q00A83Q00024Q00A83Q001E3Q0006AE00240008000100032Q00A83Q00204Q00A83Q00214Q00A83Q00193Q0006AE00250009000100012Q00A83Q00063Q0006AE0026000A000100012Q00A83Q00023Q0006AE0027000B000100012Q00A83Q00053Q0006AE0028000C000100012Q00A83Q00063Q0002420029000D3Q0006AE002A000E000100022Q00A83Q00284Q00A83Q00293Q0006AE002B000F000100012Q00A83Q002A3Q0006AE002C0010000100012Q00A83Q002A3Q0006AE002D0011000100022Q00A83Q00024Q00A83Q00063Q0006AE002E0012000100032Q00A83Q002B4Q00A83Q002C4Q00A83Q002D3Q0006AE002F0013000100012Q00A83Q00063Q0006AE00300014000100012Q00A83Q00053Q000242003100153Q000242003200163Q0006AE00330017000100072Q00A83Q002E4Q00A83Q00194Q00A83Q00314Q00A83Q00184Q00A83Q00174Q00A83Q00324Q00A83Q000A3Q0006AE00340018000100022Q00A83Q00054Q00A83Q00063Q000242003500193Q0006AE0036001A000100022Q00A83Q000F4Q00A83Q00053Q0006AE0037001B000100022Q00A83Q000F4Q00A83Q00153Q0006AE0038001C000100012Q00A83Q000F3Q0006AE0039001D000100072Q00A83Q00134Q00A83Q00114Q00A83Q00124Q00A83Q00344Q00A83Q00354Q00A83Q00104Q00A83Q00383Q0006AE003A001E0001000D2Q00A83Q00134Q00A83Q00394Q00A83Q00344Q00A83Q00354Q00A83Q00194Q00A83Q00364Q00A83Q00374Q00A83Q00124Q00A83Q00034Q00A83Q00114Q00A83Q00164Q00A83Q00144Q00A83Q00103Q0006AE003B001F000100042Q00A83Q00234Q00A83Q00194Q00A83Q00204Q00A83Q00213Q0006AE003C0020000100042Q00A83Q00344Q00A83Q00194Q00A83Q00044Q00A83Q00063Q0006AE003D0021000100142Q00A83Q000D4Q00A83Q00254Q00A83Q00334Q00A83Q001A4Q00A83Q00194Q00A83Q00264Q00A83Q00274Q00A83Q00344Q00A83Q00354Q00A83Q000E4Q00A83Q00244Q00A83Q003B4Q00A83Q000A4Q00A83Q00304Q00A83Q003C4Q00A83Q000C4Q00A83Q001D4Q00A83Q002F4Q00A83Q001C4Q00A83Q00023Q0006AE003E0022000100062Q00A83Q000B4Q00A83Q000A4Q00A83Q000D4Q00A83Q000C4Q00A83Q00194Q00A83Q003D3Q0006AE003F0023000100012Q00A83Q000A3Q0006AE00400024000100062Q00A83Q000A4Q00A83Q000D4Q00A83Q000E4Q00A83Q000C4Q00A83Q00094Q00A83Q00193Q0010A40007003900400010A40007003A003D0006AE00400025000100012Q00A83Q003D3Q0010A40007003B00400006AE00400026000100012Q00A83Q003D3Q0010A40007003C00400010A40007003D003E0010A40007003E003F0010A40007003F002E0006AE00400027000100032Q00A83Q003F4Q00A83Q00394Q00A83Q00193Q00121E004100403Q00202Q00410041004100202Q0042000700424Q004300406Q0041004300014Q004100193Q00122Q004200436Q00410002000100202Q0041000800444Q00433Q000300309B00430045004600309B00430047004800309B00430049001B2Q00730041004300012Q00663Q00013Q00288Q00034Q009C8Q00018Q00663Q00017Q00053Q0003053Q007072696E7403073Q005B53652Q6C5D2003023Q005F4703053Q00466F7267652Q033Q004C6F6701163Q00125D000100013Q00122Q000200026Q00038Q0002000200034Q00010002000100122Q000100033Q00202Q00010001000400062Q0001001500013Q00046B3Q0015000100120A000100033Q0020960001000100040020960001000100050006280001001500013Q00046B3Q0015000100120A000100033Q00203600010001000400202Q00010001000500122Q000200026Q00038Q0002000200034Q0001000200012Q00663Q00017Q00013Q0003053Q007063612Q6C03083Q00120A000300013Q0006AE00043Q000100042Q00A78Q00A88Q00A83Q00014Q00A83Q00024Q00350003000200012Q00663Q00013Q00013Q00053Q0003063Q004E6F7469667903053Q005469746C6503073Q00436F6E74656E7403083Q004475726174696F6E027Q0040000E4Q006C7Q00206Q00014Q00023Q00034Q000300013Q00102Q0002000200034Q000300023Q00102Q0002000300034Q000300033Q00062Q0003000B0001000100046B3Q000B0001001278000300053Q0010A40002000400032Q00733Q000200012Q00663Q00017Q00073Q0003043Q007479706503053Q007461626C6503063Q0072617767657403063Q006E756D626572028Q0003073Q00622Q6F6C65616E0100021E3Q00120A000200014Q00A800036Q0050000200020002002606000200070001000200046B3Q000700012Q009C00026Q004B000200023Q00120A000200034Q002C00038Q000400016Q00020004000200122Q000300016Q000400026Q00030002000200262Q000300130001000400046B3Q0013000100201F3Q000100052Q009C000300014Q004B000300023Q00120A000300014Q00A8000400024Q005000030002000200264E0003001B0001000600046B3Q001B000100201F3Q000100072Q009C000300014Q004B000300024Q009C00036Q004B000300024Q00663Q00017Q00043Q0003043Q007479706503053Q007461626C65030C3Q0044617368432Q6F6C646F776E03073Q0044617368696E6701183Q00120A000100014Q00A800026Q0050000100020002002606000100070001000200046B3Q000700012Q009C00016Q004B000100024Q009C00016Q006E00028Q00035Q00122Q000400036Q00020004000200062Q0002000F00013Q00046B3Q000F00012Q009C000100014Q00A700026Q00A800035Q001278000400044Q00190002000400020006280002001600013Q00046B3Q001600012Q009C000100014Q004B000100024Q00663Q00017Q00083Q0003043Q007479706503063Q00737472696E6703053Q006C6F776572030A3Q006E6F6D6F76656D656E74030F3Q0064697361626C656261636B7061636B03063Q006E6F64617368030B3Q0064697361626C6564617368030E3Q006E6F64617368632Q6F6C646F776E01173Q00120A000100014Q00A800026Q0050000100020002002606000100070001000200046B3Q000700012Q009C00016Q004B000100023Q00202300013Q00032Q0050000100020002002606000100140001000400046B3Q00140001002606000100140001000500046B3Q00140001002606000100140001000600046B3Q00140001002606000100140001000700046B3Q00140001002606000100140001000800046B3Q001400012Q006900026Q009C000200014Q004B000200024Q00663Q00017Q00053Q0003093Q00436F2Q6E6563746564030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F7465030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637400194Q00A77Q0006283Q000800013Q00046B3Q000800012Q00A77Q0020965Q00010006283Q000800013Q00046B3Q000800012Q00663Q00014Q00A73Q00013Q00208D5Q000200122Q000200036Q000300018Q0003000200064Q00100001000100046B3Q001000012Q00663Q00013Q00209600013Q00040020230001000100050006AE00033Q000100032Q00A73Q00024Q00A73Q00034Q00A73Q00044Q00190001000300022Q000100016Q00663Q00013Q00013Q00063Q0003043Q00722Q6F742Q033Q0063747803043Q0074696D6503023Q006F7303053Q00636C6F636B030F3Q0053652Q6C436F6E6669726D4D69736302114Q008C00025Q00102Q000200016Q00025Q00102Q0002000200014Q00025Q00122Q000300043Q00202Q0003000300054Q00030001000200102Q00020003000300264Q00100001000600046B3Q001000012Q0001000100013Q00120A000200043Q0020960002000200052Q00970002000100022Q0001000200024Q00663Q00017Q000E3Q00030E3Q0046696E6446697273744368696C64030E3Q004469616C6F67756552656D6F746503023Q006F7303053Q00636C6F636B027Q004003043Q00722Q6F7403043Q0074696D652Q033Q00637478030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637403043Q007461736B03043Q0077616974029A5Q99A93F030A3Q00446973636F2Q6E65637402524Q002F00028Q0002000100014Q000200013Q00202Q00020002000100122Q000400026Q000500016Q00020005000200062Q0002000B00013Q00046B3Q000B000100060F3Q000E0001000100046B3Q000E00012Q009C00036Q0009000400044Q005F000300033Q00120A000300033Q0020960003000300042Q0097000300010002000684000400140001000100046B3Q00140001001278000400054Q00A7000500023Q0020960005000500060006900005002400013Q00046B3Q0024000100120A000500033Q0020540005000500044Q0005000100024Q000600023Q00202Q0006000600074Q00050005000600062Q000500240001000400046B3Q002400012Q009C000500014Q00A7000600023Q0020960006000600082Q005F000500034Q009C00056Q0009000600073Q00209600080002000900202300080008000A0006AE000A3Q000100032Q00A88Q00A83Q00054Q00A83Q00064Q00190008000A00022Q00A8000700083Q00060F0005004A0001000100046B3Q004A000100120A000800033Q0020960008000800042Q00970008000100022Q00260008000800030006AB0008004A0001000400046B3Q004A000100120A0008000B3Q00207600080008000C00122Q0009000D6Q0008000200014Q000800023Q00202Q00080008000600062Q0008002E00013Q00046B3Q002E000100120A000800033Q0020540008000800044Q0008000100024Q000900023Q00202Q0009000900074Q00080008000900062Q0008002E0001000400046B3Q002E00012Q009C000500014Q00A7000800023Q00209600060008000800046B3Q002E00010006280007004E00013Q00046B3Q004E000100202300080007000E2Q00350008000200012Q00A8000800054Q00A8000900064Q005F000800034Q00663Q00013Q00017Q0002074Q00A700025Q0006903Q00060001000200046B3Q000600012Q009C000200014Q0001000200014Q0001000100024Q00663Q00017Q00063Q0003023Q006F7303053Q00636C6F636B025Q0020AC4003303Q0052657573696E67206361636865642053652Q6C436F6E6669726D20636F6E7465787420286E6F2074656C65706F727429030D3Q004469616C6F6775654576656E7403053Q007063612Q6C011D4Q00A700015Q00060F000100050001000100046B3Q000500012Q009C00016Q004B000100023Q00120A000100013Q0020630001000100024Q0001000100024Q000200016Q000100010002000E2Q0003000E0001000100046B3Q000E00012Q009C00016Q004B000100024Q00A7000100023Q001278000200044Q00350001000200010006283Q001A00013Q00046B3Q001A000100209600013Q00050006280001001A00013Q00046B3Q001A000100120A000100063Q0006AE00023Q000100012Q00A88Q00350001000200012Q009C000100014Q004B000100024Q00663Q00013Q00013Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00057Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00073Q00030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569030A3Q004469616C6F6775655549030F3Q004469616C6F67756548616E646C65722Q033Q00497341030B3Q004C6F63616C53637269707403053Q007063612Q6C011D4Q00A900015Q00202Q00010001000100122Q000300026Q00010003000200062Q000100070001000100046B3Q000700012Q00663Q00013Q002023000200010001001278000400034Q001900020004000200060F0002000D0001000100046B3Q000D00012Q00663Q00013Q002023000300020001001278000500044Q00190003000500020006280003001C00013Q00046B3Q001C0001002023000400030005001278000600064Q00190004000600020006280004001C00013Q00046B3Q001C000100120A000400073Q0006AE00053Q000100022Q00A83Q00034Q00A88Q00350004000200012Q00663Q00013Q00013Q00013Q0003083Q0044697361626C6564000A4Q00A78Q00A7000100013Q0006280001000700013Q00046B3Q000700012Q009C000100013Q00060F000100080001000100046B3Q000800012Q009C00015Q0010A43Q000100012Q00663Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q00536572766963657303103Q0050726F78696D69747953657276696365030F3Q004469616C6F6775655365727669636503023Q00524603023Q005245030D3Q00466F7263654469616C6F67756503083Q004469616C6F677565030A3Q0052756E436F2Q6D616E64030D3Q004469616C6F6775654576656E7400474Q00337Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00046B3Q0009000100202300013Q0001001278000300034Q001900010003000200069E0002000E0001000100046B3Q000E0001002023000200010001001278000400044Q001900020004000200069E000300130001000200046B3Q00130001002023000300020001001278000500054Q001900030005000200069E000400180001000300046B3Q00180001002023000400030001001278000600064Q001900040006000200069E0005001D0001000300046B3Q001D0001002023000500030001001278000700074Q001900050007000200069E000600220001000400046B3Q00220001002023000600040001001278000800084Q001900060008000200069E000700270001000500046B3Q00270001002023000700050001001278000900084Q001900070009000200069E0008002C0001000500046B3Q002C0001002023000800050001001278000A00094Q00190008000A00022Q001200093Q000400069E000A00320001000600046B3Q00320001002023000A00060001001278000C000A4Q0019000A000C00020010A40009000A000A00069E000A00380001000600046B3Q00380001002023000A00060001001278000C000B4Q0019000A000C00020010A40009000B000A00069E000A003E0001000700046B3Q003E0001002023000A00070001001278000C000C4Q0019000A000C00020010A40009000C000A00069E000A00440001000800046B3Q00440001002023000A00080001001278000C000D4Q0019000A000C00020010A40009000D000A2Q004B000900024Q00663Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q65647920436579000B4Q00337Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00046B3Q0009000100202300013Q0001001278000300034Q00190001000300022Q004B000100024Q00663Q00017Q00023Q0003063Q0055736572496403083Q00746F6E756D62657201164Q00A700015Q0006280001000500013Q00046B3Q000500012Q00A700015Q00209600010001000100060F000100090001000100046B3Q000900012Q009C00026Q004B000200023Q0006903Q000D0001000100046B3Q000D00012Q009C000200014Q004B000200023Q00120A000200024Q00A800036Q0050000200020002000602000200130001000100046B3Q001300012Q006900036Q009C000300014Q004B000300024Q00663Q00017Q00083Q0003043Q007479706503053Q007461626C6503063Q0072617767657403043Q004D697363030A3Q0045717569706D656E747303053Q00706169727303063Q00737472696E6703063Q006E756D62657201333Q00120A000100014Q00A800026Q0050000100020002002606000100070001000200046B3Q000700012Q009C00016Q004B000100023Q00120A000100013Q00122D000200036Q00035Q00122Q000400046Q000200046Q00013Q000200262Q000100170001000200046B3Q0017000100120A000100013Q001216000200036Q00035Q00122Q000400056Q000200046Q00013Q000200262Q000100190001000200046B3Q001900012Q009C000100014Q004B000100023Q00120A000100064Q00A800026Q001800010002000300046B3Q002E000100120A000600014Q00A8000700044Q005000060002000200264E0006002E0001000700046B3Q002E000100120A000600014Q00A8000700054Q00500006000200020026060006002C0001000800046B3Q002C000100120A000600014Q00A8000700054Q005000060002000200264E0006002E0001000200046B3Q002E00012Q009C000600014Q004B000600023Q00065C0001001D0001000200046B3Q001D00012Q009C00016Q004B000100024Q00663Q00017Q00083Q0003053Q00706169727303043Q007479706503053Q007461626C6503063Q0072617767657403043Q004461746103093Q00496E76656E746F727903043Q005461677303063Q0055736572496401473Q00120A000200014Q00A800036Q001800020002000400046B3Q0043000100120A000700024Q00A8000800064Q005000070002000200264E000700430001000300046B3Q0043000100120A000700044Q002B000800063Q00122Q000900056Q00070009000200122Q000800026Q000900076Q00080002000200262Q000800370001000300046B3Q0037000100120A000800044Q002B000900073Q00122Q000A00066Q0008000A000200122Q000900026Q000A00086Q00090002000200262Q000900370001000300046B3Q0037000100120A000900044Q002B000A00063Q00122Q000B00076Q0009000B000200122Q000A00026Q000B00096Q000A0002000200262Q000A002D0001000300046B3Q002D00012Q00A7000A5Q0012A2000B00046Q000C00093Q00122Q000D00086Q000B000D6Q000A3Q000200062Q000A002D00013Q00046B3Q002D00012Q004B000700023Q00060F000900370001000100046B3Q0037000100060F000100370001000100046B3Q003700012Q00A7000A00014Q00A8000B00084Q0050000A00020002000628000A003700013Q00046B3Q003700012Q00A8000100073Q00120A000800044Q00A8000900063Q001278000A00064Q00190008000A000200060F000100430001000100046B3Q004300012Q00A7000900014Q00A8000A00084Q00500009000200020006280009004300013Q00046B3Q004300012Q00A8000100063Q00065C000200040001000200046B3Q000400012Q004B000100024Q00663Q00017Q00053Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6500193Q00120A3Q00013Q00120A000100024Q00503Q000200020026063Q00070001000300046B3Q000700012Q00098Q004B3Q00023Q00120A3Q00043Q00120A000100024Q009C000200014Q00573Q000200010006283Q001200013Q00046B3Q0012000100120A000200014Q00A8000300014Q0050000200020002002606000200140001000500046B3Q001400012Q0009000200024Q004B000200024Q00A700026Q00A8000300014Q004C000200034Q009100026Q00663Q00017Q00063Q0003043Q007479706503053Q00646562756703053Q007461626C65030B3Q00676574726567697374727903083Q0066756E6374696F6E03053Q007063612Q6C001F3Q00120A3Q00013Q00120A000100024Q00503Q0002000200264E3Q000B0001000300046B3Q000B000100120A3Q00013Q00120A000100023Q0020960001000100042Q00503Q000200020026063Q000D0001000500046B3Q000D00012Q00098Q004B3Q00023Q00120A3Q00063Q00120A000100023Q0020960001000100042Q00183Q000200010006283Q001800013Q00046B3Q0018000100120A000200014Q00A8000300014Q00500002000200020026060002001A0001000300046B3Q001A00012Q0009000200024Q004B000200024Q00A700026Q00A8000300014Q004C000200034Q009100026Q00663Q00017Q00103Q00030E3Q0046696E6446697273744368696C64030D3Q005265706C696361436C69656E7403053Q007063612Q6C03073Q007265717569726503043Q007479706503053Q007461626C6503063Q0055736572496403083Q005265706C6963617303093Q005F7265706C6963617303083Q007265706C6963617303053Q00706169727303063Q0072617767657403043Q005461677303043Q004461746103083Q00746F6E756D62657203093Q00496E76656E746F727900624Q00A97Q00206Q000100122Q000200028Q0002000200064Q00080001000100046B3Q000800012Q0009000100014Q004B000100023Q00120A000100033Q00120A000200044Q00A800036Q00570001000300020006280001001300013Q00046B3Q0013000100120A000300054Q00A8000400024Q0050000300020002002606000300150001000600046B3Q001500012Q0009000300034Q004B000300024Q00A7000300013Q0006280003001A00013Q00046B3Q001A00012Q00A7000300013Q00209600030003000700060F0003001E0001000100046B3Q001E00012Q0009000400044Q004B000400024Q0012000400033Q00209600050002000800209600060002000900209600070002000A2Q003B00040003000100120A0005000B4Q00A8000600044Q001800050002000700046B3Q005D000100120A000A00054Q00A8000B00094Q0050000A0002000200264E000A005D0001000600046B3Q005D000100120A000A000B4Q00A8000B00094Q0018000A0002000C00046B3Q005B000100120A000F00054Q00A80010000E4Q0050000F0002000200264E000F005B0001000600046B3Q005B000100120A000F000C4Q00410010000E3Q00122Q0011000D6Q000F0011000200122Q0010000C6Q0011000E3Q00122Q0012000E6Q00100012000200122Q001100056Q0012000F6Q00110002000200262Q0011005B0001000600046B3Q005B000100120A001100054Q00A8001200104Q005000110002000200264E0011005B0001000600046B3Q005B000100120A0011000C4Q00A80012000F3Q001278001300074Q0019001100130002000602001100520001000300046B3Q0052000100120A0012000F4Q00A8001300114Q00500012000200020006900012005B0001000300046B3Q005B000100120A001200053Q0012160013000C6Q001400103Q00122Q001500106Q001300156Q00123Q000200262Q0012005B0001000600046B3Q005B00012Q004B001000023Q00065C000A00300001000200046B3Q0030000100065C000500270001000200046B3Q002700012Q0009000500054Q004B000500024Q00663Q00017Q00033Q0003023Q00676303083Q00726567697374727903073Q007265706C696361001A4Q00A78Q00973Q000100020006283Q000700013Q00046B3Q000700012Q00A800015Q001278000200014Q005F000100034Q00A7000100014Q00970001000100022Q00A83Q00013Q0006283Q000F00013Q00046B3Q000F00012Q00A800015Q001278000200024Q005F000100034Q00A7000100024Q00970001000100022Q00A83Q00013Q0006283Q001700013Q00046B3Q001700012Q00A800015Q001278000200034Q005F000100034Q0009000100024Q005F000100034Q00663Q00017Q000E3Q0003043Q007479706503053Q00676574676303083Q0066756E6374696F6E03053Q007063612Q6C03053Q007461626C6503063Q0055736572496403053Q00706169727303063Q0072617767657403053Q00546F6B656E03043Q005461677303043Q0044617461030C3Q00506C6179657253746174757303083Q00746F6E756D62657203083Q004D6F76656D656E7400593Q00120A3Q00013Q00120A000100024Q00503Q000200020026063Q00070001000300046B3Q000700012Q00098Q004B3Q00023Q00120A3Q00043Q00120A000100024Q009C000200014Q00573Q000200010006283Q001200013Q00046B3Q0012000100120A000200014Q00A8000300014Q0050000200020002002606000200140001000500046B3Q001400012Q0009000200024Q004B000200024Q00A700025Q0006280002001900013Q00046B3Q001900012Q00A700025Q00209600020002000600060F0002001D0001000100046B3Q001D00012Q0009000300034Q004B000300023Q00120A000300074Q00A8000400014Q001800030002000500046B3Q0054000100120A000800014Q00A8000900074Q005000080002000200264E000800540001000500046B3Q0054000100120A000800084Q001D000900073Q00122Q000A00096Q0008000A000200122Q000900086Q000A00073Q00122Q000B000A6Q0009000B000200122Q000A00086Q000B00073Q00122Q000C000B6Q000A000C000200262Q000800540001000C00046B3Q0054000100120A000B00014Q00A8000C000A4Q0050000B0002000200264E000B00540001000500046B3Q0054000100120A000B00014Q00A8000C00094Q0050000B0002000200264E000B004B0001000500046B3Q004B000100120A000B00084Q00A8000C00093Q001278000D00064Q0019000B000D0002000602000B00490001000200046B3Q0049000100120A000C000D4Q00A8000D000B4Q0050000C00020002000690000C00540001000200046B3Q005400012Q004B000A00023Q00046B3Q0054000100120A000B00013Q001216000C00086Q000D000A3Q00122Q000E000E6Q000C000E6Q000B3Q000200262Q000B00540001000500046B3Q005400012Q004B000A00023Q00065C000300210001000200046B3Q002100012Q0009000300034Q004B000300024Q00663Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403093Q0050726F78696D697479030A3Q0047722Q656479204365792Q033Q0049734103053Q004D6F64656C030B3Q005072696D6172795061727403103Q0048756D616E6F6964522Q6F745061727403063Q00434672616D6503083Q004765745069766F7403083Q00426173655061727403083Q00506F736974696F6E030A3Q004C2Q6F6B566563746F72026Q00144000324Q00337Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00046B3Q0009000100202300013Q0001001278000300034Q001900010003000200060F0001000D0001000100046B3Q000D00012Q0009000200024Q004B000200024Q0009000200023Q002023000300010004001278000500054Q00190003000500020006280003002200013Q00046B3Q0022000100209600030001000600060F000300190001000100046B3Q00190001002023000300010001001278000500074Q00190003000500020006280003001E00013Q00046B3Q001E0001002096000400030008000684000200210001000400046B3Q002100010020230004000100092Q00500004000200022Q00A8000200043Q00046B3Q002800010020230003000100040012780005000A4Q00190003000500020006280003002800013Q00046B3Q002800010020960002000100080006280002002F00013Q00046B3Q002F000100209600030002000B00209600040002000C0020AC00040004000D2Q002E0003000300042Q004B000300024Q0009000300034Q004B000300024Q00663Q00017Q00053Q0003043Q007479706503093Q004661766F726974657303053Q007461626C6503053Q0070616972733Q01114Q001200015Q0006283Q000F00013Q00046B3Q000F000100120A000200013Q00209600033Q00022Q005000020002000200264E0002000F0001000300046B3Q000F000100120A000200043Q00209600033Q00022Q001800020002000400046B3Q000D000100201F00010005000500065C0002000C0001000200046B3Q000C00012Q004B000100024Q00663Q00017Q00053Q0003043Q007479706503063Q00737472696E6703053Q006D61746368034A3Q005E25782578257825782578257825782578252D2578257825782578252D2578257825782578252D2578257825782578252D257825782578257825782578257825782578257825782578240001103Q00120A000100014Q00A800026Q0050000100020002002606000100070001000200046B3Q000700012Q009C00016Q004B000100023Q00202300013Q0003001278000300044Q001900010003000200264E0001000D0001000500046B3Q000D00012Q006900016Q009C000100014Q004B000100024Q00663Q00017Q00173Q0003283Q00706C617965722064617461206E6F7420666F756E6420286E6F206D6574686F6420776F726B65642903173Q00506C61796572206461746120666F756E64207669613A2003093Q00496E76656E746F727903223Q00696E76656E746F7279206E6F7420666F756E6420696E20706C617965722064617461028Q0003053Q00706169727303043Q007479706503063Q00737472696E6703063Q006E756D626572030D3Q00536B69704661766F726974657303043Q004D69736303053Q007461626C6503043Q004E616D6503083Q005175616E7469747903043Q004755494403043Q004F72657303053Q0052756E657303073Q005570677261646503043Q0054797065026Q00F03F03043Q006E6578740003173Q006E6F2073652Q6C61626C65206974656D7320666F756E6400984Q00A78Q00383Q0001000100060F3Q00070001000100046B3Q000700012Q0009000200023Q001278000300014Q005F000200034Q00A7000200013Q00120D000300026Q000400016Q0003000300044Q00020002000100202Q00023Q000300062Q000200120001000100046B3Q001200012Q0009000300033Q001278000400044Q005F000300034Q00A7000300024Q009300048Q0003000200024Q00045Q00122Q000500053Q00122Q000600066Q000700026Q00060002000800044Q003D000100120A000B00074Q00A8000C00094Q0050000B0002000200264E000B003D0001000800046B3Q003D000100120A000B00074Q00A8000C000A4Q0050000B0002000200264E000B003D0001000900046B3Q003D0001000E880005003D0001000A00046B3Q003D00012Q00A7000B00034Q0052000B000B000900060F000B003D0001000100046B3Q003D00012Q00A7000B00044Q0052000B000B000900060F000B003D0001000100046B3Q003D00012Q00A7000B00054Q00A8000C00094Q0050000B0002000200060F000B003D0001000100046B3Q003D00012Q00A7000B00063Q002096000B000B000A000628000B003B00013Q00046B3Q003B00012Q0052000B0003000900060F000B003D0001000100046B3Q003D00012Q003900040009000A2Q002E00050005000A00065C0006001B0001000200046B3Q001B000100209600060002000B00120A000700074Q00A8000800064Q005000070002000200264E0007008B0001000C00046B3Q008B000100120A000700064Q00A8000800064Q001800070002000900046B3Q0089000100120A000C00074Q00A8000D000B4Q0050000C0002000200264E000C00890001000C00046B3Q00890001002096000C000B000D002096000D000B000E002096000E000B000F2Q009C000F5Q000628000C007000013Q00046B3Q00700001000628000D007000013Q00046B3Q0070000100120A001000074Q00A80011000D4Q005000100002000200264E001000700001000900046B3Q00700001000E88000500700001000D00046B3Q007000012Q00A7001000044Q005200100010000C0006280010007000013Q00046B3Q007000012Q00A7001000063Q00209600100010000A0006280010006800013Q00046B3Q006800012Q005200100003000C00060F001000700001000100046B3Q007000012Q005200100004000C00060F0010006C0001000100046B3Q006C0001001278001000054Q002E00100010000D2Q00390004000C00102Q002E00050005000D2Q009C000F00013Q00060F000F00890001000100046B3Q00890001000628000E008900013Q00046B3Q008900010020960010000B001000060F0010007E0001000100046B3Q007E00010020960010000B001100060F0010007E0001000100046B3Q007E00010020960010000B001200060F0010007E0001000100046B3Q007E00010020960010000B001300060F001000890001000100046B3Q008900012Q00A7001100063Q00209600110011000A0006280011008700013Q00046B3Q008700012Q005200110003000E00060F001100890001000100046B3Q0089000100201F0004000E00140020AD00050005001400065C000700490001000200046B3Q0049000100120A000700154Q00A8000800044Q005000070002000200264E000700930001001600046B3Q009300012Q0009000700073Q001278000800174Q005F000700034Q00A8000700044Q0009000800084Q00A8000900054Q0043000700024Q00663Q00017Q00043Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D6503093Q00436861726163746572000F4Q00307Q00206Q000100122Q000200028Q0002000200064Q000B00013Q00046B3Q000B000100202300013Q00012Q00A7000300013Q0020960003000300032Q004C000100034Q009100016Q00A7000100013Q0020960001000100042Q004B000100024Q00663Q00017Q00023Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727401073Q00069E0001000500013Q00046B3Q0005000100202300013Q0001001278000300024Q00190001000300022Q004B000100024Q00663Q00017Q00103Q0003083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503103Q0053652Q6C4D6F64756C6543617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003063Q00506172656E74001D4Q00A77Q0006283Q000400013Q00046B3Q000400012Q00663Q00013Q00120A3Q00013Q0020A65Q000200122Q000100038Q000200029Q009Q0000304Q000400059Q0000122Q000100073Q00202Q00010001000200122Q000200083Q00122Q000300093Q00122Q000400086Q00010004000200104Q000600019Q0000304Q000A000B9Q0000304Q000C000D9Q0000304Q000E000F9Q004Q000100013Q00104Q001000016Q00017Q00043Q0003063Q00506172656E7403063Q00434672616D652Q033Q006E6577028Q0001144Q00A700015Q0006280001000800013Q00046B3Q000800010006283Q000800013Q00046B3Q0008000100209600013Q000100060F000100090001000100046B3Q000900012Q00663Q00014Q00A700015Q00203C00023Q000200122Q000300023Q00202Q00030003000300122Q000400046Q000500013Q00122Q000600046Q0003000600024Q00020002000300102Q0001000200026Q00017Q00013Q0003073Q0044657374726F7900094Q00A77Q0006283Q000800013Q00046B3Q000800012Q00A77Q0020235Q00012Q00353Q000200012Q00098Q00018Q00663Q00017Q00113Q00030A3Q00446973636F2Q6E656374030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E64010003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103073Q0044657374726F7903103Q0053652Q6C426F6479506F736974696F6E00504Q009C8Q00018Q00A73Q00013Q0006283Q000A00013Q00046B3Q000A00012Q00A73Q00013Q0020235Q00012Q00353Q000200012Q00098Q00013Q00014Q00A73Q00023Q0006283Q001200013Q00046B3Q001200012Q00A73Q00023Q0020235Q00012Q00353Q000200012Q00098Q00013Q00024Q00A73Q00034Q00973Q000100020006283Q003700013Q00046B3Q003700012Q00A7000100044Q000800028Q00010002000200202Q00023Q000200122Q000400036Q00020004000200062Q0001002400013Q00046B3Q0024000100120A000300053Q00205600030003000600102Q00010004000300122Q000300053Q00202Q00030003000600102Q0001000700030006280002002A00013Q00046B3Q002A00010020960003000200080006280003002A00013Q00046B3Q002A000100309B00020008000900120A0003000A3Q00202300043Q000B2Q008F000400054Q00AA00033Q000500046B3Q0035000100202300080007000C001278000A000D4Q00190008000A00020006280008003500013Q00046B3Q0035000100309B0007000E000F00065C0003002F0001000200046B3Q002F00012Q00A7000100053Q0006280001003F00013Q00046B3Q003F00012Q00A7000100053Q0020230001000100102Q00350001000200012Q0009000100014Q0001000100053Q0006283Q004D00013Q00046B3Q004D00012Q00A7000100044Q00A800026Q00500001000200020006280001004D00013Q00046B3Q004D0001002023000200010002001278000400114Q00190002000400020006280002004D00013Q00046B3Q004D00010020230003000200102Q00350003000200012Q00A7000100064Q00170001000100012Q00663Q00017Q00163Q0003043Q007461736B03043Q0077616974029A5Q99B93F030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403213Q00466C79546F206661696C65643A20436861726163746572206E6F7420666F756E64030D3Q00506C6174666F726D5374616E642Q0103163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964650100030B3Q00466C79696E6720746F3A202Q033Q004E504303093Q0048656172746265617403073Q00436F2Q6E65637402564Q00A700025Q0006280002000900013Q00046B3Q000900012Q00A7000200014Q009400020001000100122Q000200013Q00202Q00020002000200122Q000300036Q0002000200012Q00A7000200024Q00A30002000100024Q000300036Q000400026Q00030002000200062Q000400130001000200046B3Q00130001002023000400020004001278000600054Q00190004000600020006280003001700013Q00046B3Q0017000100060F0004001B0001000100046B3Q001B00012Q00A7000500043Q001278000600064Q00350005000200012Q00663Q00013Q00309B0004000700080012A10005000A3Q00202Q00050005000B00102Q00030009000500122Q0005000A3Q00202Q00050005000B00102Q0003000C00050012A00005000D3Q00202Q00060002000E4Q000600076Q00053Q000700044Q002D0001002023000A0009000F001278000C00104Q0019000A000C0002000628000A002D00013Q00046B3Q002D000100309B00090011001200065C000500270001000200046B3Q002700012Q009C000500014Q007C00058Q000500056Q0005000100014Q000500066Q000600036Q0005000200014Q000500043Q00122Q000600133Q00062Q0007003B0001000100046B3Q003B0001001278000700144Q00990006000600072Q00350005000200012Q00A7000500083Q0020960005000500150020230005000500160006AE00073Q000100022Q00A78Q00A73Q00024Q00240005000700024Q000500076Q000500083Q00202Q00050005001500202Q0005000500160006AE000700010001000A2Q00A78Q00A73Q00024Q00A73Q00034Q00A73Q00064Q00A88Q00A73Q000A4Q00A73Q00044Q00A73Q00014Q00A73Q000B4Q00A73Q000C4Q00190005000700022Q0001000500094Q00663Q00013Q00023Q00063Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465012Q001A4Q00A77Q00060F3Q00040001000100046B3Q000400012Q00663Q00014Q00A73Q00014Q00973Q0001000200060F3Q00090001000100046B3Q000900012Q00663Q00013Q00120A000100013Q00202300023Q00022Q008F000200034Q00AA00013Q000300046B3Q00170001002023000600050003001278000800044Q00190006000800020006280006001700013Q00046B3Q001700010020960006000500050006280006001700013Q00046B3Q0017000100309B00050005000600065C0001000E0001000200046B3Q000E00012Q00663Q00017Q00263Q00030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E642Q0103083Q00506F736974696F6E03093Q004D61676E697475646503163Q00412Q72697665642061742064657374696E6174696F6E026Q11913F03043Q00556E697403043Q006D6174682Q033Q006D696E03083Q00496E7374616E63652Q033Q006E657703083Q00426F64794779726F03093Q004D6178546F7271756503073Q00566563746F7233024Q00652QCD4103013Q0050025Q0088C34003013Q0044026Q00594003063Q00506172656E7403013Q005803013Q005903013Q005A029A5Q99B93F03063Q00434672616D6503063Q006C2Q6F6B417403103Q0053652Q6C426F6479506F736974696F6E030C3Q00426F6479506F736974696F6E03043Q004E616D6503083Q004D6178466F726365024Q0080842E41025Q006AE840025Q00408F4003163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479017F4Q00A700015Q00060F000100040001000100046B3Q000400012Q00663Q00014Q00A7000100014Q00A30001000100024Q000200026Q000300016Q00020002000200062Q0003000E0001000100046B3Q000E0001002023000300010001001278000500024Q00190003000500020006280002001200013Q00046B3Q0012000100060F000300130001000100046B3Q001300012Q00663Q00014Q00A7000400034Q00A8000500024Q003500040002000100209600040003000300060F0004001A0001000100046B3Q001A000100309B0003000300040020960004000200052Q009F000500046Q00050005000400202Q0006000500064Q000700053Q00062Q000600270001000700046B3Q002700012Q00A7000700063Q00124F000800076Q0007000200014Q000700076Q0007000100016Q00014Q00A7000700083Q0006840008002B00013Q00046B3Q002B0001001278000800084Q008600070007000800203A00080005000900122Q0009000A3Q00202Q00090009000B4Q000A00076Q000B00066Q0009000B00024Q000A000800094Q000A0004000A4Q000B00093Q00062Q000B004A0001000100046B3Q004A000100120A000B000C3Q00209A000B000B000D00122Q000C000E6Q000B000200024Q000B00096Q000B00093Q00122Q000C00103Q00202Q000C000C000D00122Q000D00113Q00122Q000E00113Q00122Q000F00116Q000C000F000200102Q000B000F000C4Q000B00093Q00302Q000B001200134Q000B00093Q00302Q000B001400154Q000B00093Q00102Q000B0016000200120A000B00103Q002095000B000B000D4Q000C00043Q00202Q000C000C001700202Q000D000A00184Q000E00043Q00202Q000E000E00194Q000B000E00024Q000C000B000A00202Q000C000C0006000E2Q001A005D0001000C00046B3Q005D00012Q00A7000D00093Q001229000E001B3Q00202Q000E000E001C4Q000F000A6Q0010000B6Q000E0010000200102Q000D001B000E002023000D00020001001278000F001D4Q0019000D000F000200060F000D00720001000100046B3Q0072000100120A000E000C3Q00206F000E000E000D00122Q000F001E6Q000E000200024Q000D000E3Q00302Q000D001F001D00122Q000E00103Q00202Q000E000E000D00122Q000F00213Q00122Q001000213Q00122Q001100216Q000E0011000200102Q000D0020000E00302Q000D0012002200302Q000D0014002300102Q000D001600020010A4000D0005000A001246000E001B3Q00202Q000E000E000D4Q000F000A6Q000E0002000200102Q0002001B000E00122Q000E00103Q00202Q000E000E002500102Q00020024000E00122Q000E00103Q00202Q000E000E002500102Q00020026000E6Q00017Q00103Q00030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503053Q007063612Q6C010003103Q0053652Q6C4469616C6F6775654D697363026Q00F83F030D3Q004469616C6F6775654576656E7403043Q007461736B03043Q0077616974026Q00E03F00030F3Q0053652Q6C436F6E6669726D4D697363027Q004003383Q005761726E696E673A2053652Q6C436F6E6669726D4D697363206E6F74206F627365727665642C20636F6E74696E75696E6720616E7977617903023Q006F7303053Q00636C6F636B02743Q0006283Q000A00013Q00046B3Q000A000100209600023Q00010006280002000A00013Q00046B3Q000A000100209600023Q00020006280002000A00013Q00046B3Q000A000100060F0001000C0001000100046B3Q000C00012Q009C00026Q004B000200023Q00120A000200033Q0006AE00033Q000100022Q00A88Q00A83Q00014Q00180002000200030006280002002600013Q00046B3Q00260001002606000300260001000400046B3Q002600012Q00A700045Q001278000500053Q001278000600064Q00190004000600020006280004002600013Q00046B3Q0026000100209600053Q00070006280005002600013Q00046B3Q0026000100120A000500033Q0006AE00060001000100012Q00A88Q003500050002000100120A000500033Q0006AE00060002000100012Q00A88Q00350005000200012Q009C00045Q00120A000500033Q0006AE00060003000100022Q00A88Q00A83Q00014Q00180005000200062Q00A8000300064Q00A8000200053Q0006280002003300013Q00046B3Q00330001002606000300330001000400046B3Q003300012Q009C000400013Q00060F000400430001000100046B3Q0043000100120A000500083Q0020960005000500090012780006000A4Q003500050002000100120A000500033Q0006AE00060004000100022Q00A88Q00A83Q00014Q00180005000200060006280005004300013Q00046B3Q00430001002606000600430001000400046B3Q004300012Q009C000400013Q00060F0004004A0001000100046B3Q004A00010006280002004A00013Q00046B3Q004A000100264E0003004A0001000B00046B3Q004A00012Q009C000400013Q00060F0004004E0001000100046B3Q004E00012Q009C00056Q004B000500024Q00A700055Q0012780006000C3Q0012780007000D4Q005700050007000600060F0005005E0001000100046B3Q005E000100120A000700083Q00207F00070007000900122Q0008000A6Q0007000200014Q00075Q00122Q0008000C3Q00122Q0009000D6Q0007000900084Q000600086Q000500073Q00060F000500630001000100046B3Q006300012Q00A7000700013Q0012780008000E4Q00350007000200010006280006006A00013Q00046B3Q006A00012Q0001000600023Q00120A0007000F3Q0020960007000700102Q00970007000100022Q0001000700033Q00209600073Q00070006280007007100013Q00046B3Q0071000100120A000700033Q0006AE00080005000100012Q00A88Q00350007000200012Q009C000700014Q004B000700024Q00663Q00013Q00063Q00023Q0003083Q004469616C6F677565030C3Q00496E766F6B6553657276657200074Q005A7Q00206Q000100206Q00024Q000200018Q00029Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00057Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00057Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q00317Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q00466F7263654469616C6F677565030C3Q00496E766F6B65536572766572030F3Q0053652Q6C436F6E6669726D4D69736300084Q00317Q00206Q000100206Q00024Q000200013Q00122Q000300038Q00039Q008Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q004F70656E656400064Q00057Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q000D3Q00030E3Q0046696E6446697273744368696C6403063Q00537461747573030F3Q0044697361626C654261636B7061636B03283Q0052656D6F76696E672044697361626C654261636B7061636B207461672066726F6D2053746174757303053Q007063612Q6C030D3Q004469616C6F6775654576656E7403093Q00506C61796572477569030A3Q004469616C6F677565554903053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q0047756942752Q746F6E03113Q00526573706F6E736542692Q6C626F617264014D3Q00060F3Q00030001000100046B3Q000300012Q00663Q00014Q00A700016Q00970001000100020006280001001900013Q00046B3Q00190001002023000200010001001278000400024Q00190002000400020006280002001900013Q00046B3Q00190001002023000300020001001278000500034Q00190003000500020006280003001800013Q00046B3Q001800012Q00A7000400013Q001278000500044Q003500040002000100120A000400053Q0006AE00053Q000100012Q00A83Q00034Q00350004000200012Q005500035Q00209600023Q00060006280002002000013Q00046B3Q0020000100120A000200053Q0006AE00030001000100012Q00A88Q003500020002000100120A000200053Q0006AE00030002000100012Q00A73Q00024Q00070002000200014Q000200033Q00202Q00020002000100122Q000400076Q00020004000200062Q0002004C00013Q00046B3Q004C0001002023000300020001001278000500084Q00190003000500020006280003004000013Q00046B3Q0040000100120A000400093Q00202300050003000A2Q008F000500064Q00AA00043Q000600046B3Q003E000100202300090008000B001278000B000C4Q00190009000B00020006280009003D00013Q00046B3Q003D000100120A000900053Q0006AE000A0003000100012Q00A83Q00084Q00350009000200012Q005500075Q00065C000400340001000200046B3Q0034000100069E000400450001000300046B3Q004500010020230004000300010012780006000D4Q00190004000600020006280004004B00013Q00046B3Q004B000100120A000500053Q0006AE00060004000100012Q00A83Q00044Q00350005000200012Q005500036Q00663Q00013Q00053Q00013Q0003073Q0044657374726F7900044Q00A77Q0020235Q00012Q00353Q000200012Q00663Q00017Q00033Q00030D3Q004469616C6F6775654576656E74030A3Q004669726553657276657203063Q00436C6F73656400064Q00057Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030E3Q0053656C65637465644F626A65637400030E3Q00436C65617253656C656374696F6E000A4Q00327Q00304Q000100029Q0000206Q000300064Q000900013Q00046B3Q000900012Q00A77Q0020235Q00032Q00353Q000200012Q00663Q00017Q00033Q0003073Q0056697369626C650100030C3Q00496E74657261637461626C6500054Q00537Q00304Q000100029Q0000304Q000300026Q00017Q00023Q0003073Q0056697369626C65012Q00034Q00A77Q00309B3Q000100022Q00663Q00017Q00533Q0003093Q004175746F2053652Q6C03083Q004E6F206974656D73027Q004003123Q004261736B6574206275696C7420776974682003063Q00206974656D73030A3Q0052756E436F2Q6D616E64030D3Q00466F7263654469616C6F67756503083Q004469616C6F67756503113Q0052656D6F746573206E6F7420666F756E64026Q00084003183Q004E50432047722Q65647920436579206E6F7420666F756E64030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403063Q00434672616D6503093Q0057616C6B53702Q6564026Q00304003093Q004A756D70506F776572026Q004940030D3Q00666F72636554656C65706F7274030A3Q006E6F54656C65706F7274031C3Q0053652Q6C4F6E63652063612Q6C65643A206E6F54656C65706F72743D03083Q00746F737472696E6703103Q002C20666F72636554656C65706F72743D03303Q005573696E672063616368656420636F6E74657874202D20736B692Q70696E67204F70656E53652Q6C4469616C6F67756503133Q004F70656E696E67206469616C6F6775653Q2E030D3Q006469616C6F674F70656E65643D030D3Q002C206E6F54656C65706F72743D03153Q002C20486173496E697469616C697A656453652Q6C3D03143Q004E6F54656C65706F72744166746572466972737403373Q0052657475726E696E67206561726C79202D206469616C6F67206E6F74206F70656E656420616E64206E6F54656C65706F7274206D6F646503353Q004469616C6F6720746964616B20646170617420646962756B612074616E70612074656C65706F72742E2044656B617469204E50432E03163Q004E504320706F736974696F6E206E6F7420666F756E6403133Q00436861726163746572206E6F7420666F756E64031C3Q0054656C65706F7274696E6720746F2047722Q656479204365793Q2E2Q033Q006E657703163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903043Q007461736B03043Q0077616974029A5Q99B93F03173Q004661696C656420746F206F70656E206469616C6F67756503223Q0053656E64696E672053652Q6C436F6E6669726D2077697468206261736B65743Q2E03053Q007063612Q6C010003133Q00436C6F73696E67206469616C6F6775653Q2E03103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E030B3Q005072696D61727950617274028Q0003323Q0054656C65706F7274696E67206177617920746F207472692Q676572206469616C6F677565206175746F2D636C6F73653Q2E026Q33F33F03213Q0052657475726E696E6720746F206F726967696E616C20706F736974696F6E3Q2E03043Q007469636B03063Q00737472696E6703063Q00666F726D6174030D3Q00536F6C64202564206974656D73030D3Q0053652Q6C2053552Q43452Q5321030B3Q0053652Q6C206661696C6564030B3Q0053652Q6C204641494C454403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D65031B3Q0052656D6F76696E672053746174757320422Q6F6C56616C75653A20030B3Q004E756D62657256616C756503053Q006C6F77657203043Q0066696E64030C3Q0064617368632Q6F6C646F776E03253Q00526573652Q74696E67206461736820632Q6F6C646F776E204E756D62657256616C75653A202Q033Q00203D2003053Q0056616C7565030D3Q00506C6174666F726D5374616E642Q033Q0053697403163Q0057616C6B53702Q656420726573746F72656420746F2003163Q004A756D70506F77657220726573746F72656420746F2003083Q00416E63686F726564031B3Q0048756D616E6F6964522Q6F745061727420756E616E63686F72656403053Q0064656C6179026Q00E03F0113023Q00A700015Q0006280001000500013Q00046B3Q000500012Q009C00016Q004B000100024Q009C000100014Q007700018Q000100016Q000200016Q0001000200014Q000100026Q00010001000300062Q0001001C0001000100046B3Q001C00012Q009C00046Q000100046Q00A7000400033Q001278000500013Q000684000600150001000200046B3Q00150001001278000600023Q001278000700034Q00740004000700014Q000400016Q00058Q0004000200014Q00048Q000400024Q00A7000400043Q00120E000500046Q000600033Q00122Q000700056Q0005000500074Q0004000200014Q000400056Q00040001000200202Q00050004000600062Q0005002D00013Q00046B3Q002D00010020960005000400070006280005002D00013Q00046B3Q002D000100209600050004000800060F000500380001000100046B3Q003800012Q009C00056Q003400058Q000500033Q00122Q000600013Q00122Q000700093Q00122Q0008000A6Q0005000800014Q000500016Q00068Q0005000200016Q00014Q00A7000500064Q009700050001000200060F000500470001000100046B3Q004700012Q009C00066Q003400068Q000600033Q00122Q000700013Q00122Q0008000B3Q00122Q0009000A6Q0006000900014Q000600016Q00078Q0006000200016Q00014Q00A7000600074Q00A30006000100024Q000700086Q000800066Q00070002000200062Q000800510001000600046B3Q0051000100202300080006000C001278000A000D4Q00190008000A000200069E000900540001000700046B3Q0054000100209600090007000E2Q009C000A5Q0006280008005A00013Q00046B3Q005A0001002096000B0008000F00060F000B005B0001000100046B3Q005B0001001278000B00103Q0006280008006000013Q00046B3Q00600001002096000C0008001100060F000C00610001000100046B3Q00610001001278000C00123Q00069E000D006400013Q00046B3Q00640001002096000D3Q001300069E000E006700013Q00046B3Q00670001002096000E3Q00142Q00A7000F00043Q00121C001000153Q00122Q001100166Q0012000E6Q00110002000200122Q001200173Q00122Q001300166Q0014000D6Q0013000200024Q0010001000134Q000F0002000100062Q000D007600013Q00046B3Q007600012Q009C000F6Q0001000F00094Q009C000F6Q006D0010000A6Q001100046Q0010000200024Q000F00103Q00062Q000F008100013Q00046B3Q008100012Q00A7001000043Q001278001100184Q003500100002000100046B3Q008900012Q00A7001000043Q001272001100196Q0010000200014Q0010000B6Q001100046Q001200056Q0010001200024Q000F00104Q00A7001000043Q0012370011001A3Q00122Q001200166Q0013000F6Q00120002000200122Q0013001B3Q00122Q001400166Q0015000E6Q00140002000200122Q0015001C3Q00122Q001600166Q001700096Q0016000200024Q0011001100164Q00100002000100062Q000F00B40001000100046B3Q00B4000100060F000E00A30001000100046B3Q00A300012Q00A7001000093Q000628001000B400013Q00046B3Q00B400012Q00A70010000C3Q00209600100010001D000628001000B400013Q00046B3Q00B400012Q00A7001000043Q0012580011001E6Q0010000200014Q00108Q00105Q00062Q000E00AF0001000100046B3Q00AF00012Q00A7001000033Q001278001100013Q0012780012001F3Q0012780013000A4Q00730010001300012Q00A7001000014Q009C00116Q00350010000200012Q009C00106Q004B001000023Q00060F000F00EF0001000100046B3Q00EF000100060F000E00EF0001000100046B3Q00EF00012Q00A70010000D4Q009700100001000200060F001000C70001000100046B3Q00C700012Q009C00116Q003400118Q001100033Q00122Q001200013Q00122Q001300203Q00122Q0014000A6Q0011001400014Q001100016Q00128Q0011000200016Q00013Q00060F000700D40001000100046B3Q00D400012Q009C00116Q003400118Q001100033Q00122Q001200013Q00122Q001300213Q00122Q0014000A6Q0011001400014Q001100016Q00128Q0011000200016Q00014Q00A7001100043Q001298001200226Q0011000200014Q000A00013Q00122Q0011000E3Q00202Q0011001100234Q001200106Q00110002000200102Q0007000E001100122Q001100253Q00202Q00110011002600102Q00070024001100122Q001100253Q00202Q00110011002600102Q00070027001100122Q001100283Q00202Q00110011002900122Q0012002A6Q0011000200014Q001100043Q00122Q001200196Q0011000200014Q0011000B6Q001200046Q001300056Q0011001300024Q000F00113Q00060F000F000B2Q01000100046B3Q000B2Q01000628000A00FE00013Q00046B3Q00FE0001000628000900FE00013Q00046B3Q00FE0001000628000700FE00013Q00046B3Q00FE00010010A40007000E00090012A1001000253Q00202Q00100010002600102Q00070024001000122Q001000253Q00202Q00100010002600102Q0007002700102Q009C00106Q0003001000096Q00108Q00108Q001000033Q00122Q001100013Q00122Q0012002B3Q00122Q0013000A6Q0010001300014Q001000016Q00118Q0010000200016Q00014Q009C001000014Q008A001000096Q001000043Q00122Q0011002C6Q0010000200014Q00105Q00122Q0011002D3Q0006AE00123Q000100022Q00A83Q00044Q00A83Q00014Q00180011000200120006280011001B2Q013Q00046B3Q001B2Q010026060012001B2Q01002E00046B3Q001B2Q012Q009C001000013Q00120A001300283Q00204D00130013002900122Q0014002A6Q0013000200014Q001300043Q00122Q0014002F6Q0013000200014Q0013000E6Q001400046Q0013000200014Q001300016Q00148Q00130002000100062Q000E00552Q01000100046B3Q00552Q01000628000700552Q013Q00046B3Q00552Q01000628000500552Q013Q00046B3Q00552Q01002096001300050030000628001300352Q013Q00046B3Q00352Q0100209600130005003000209600130013003100060F0013003A2Q01000100046B3Q003A2Q010020960013000500320006280013003A2Q013Q00046B3Q003A2Q01002096001300050032002096001300130031000628001300552Q013Q00046B3Q00552Q0100120A001400253Q00204500140014002300122Q001500123Q00122Q001600333Q00122Q001700126Q0014001700024Q0014001300144Q001500043Q00122Q001600346Q00150002000100122Q0015000E3Q00202Q0015001500234Q001600146Q00150002000200102Q0007000E001500122Q001500253Q00202Q00150015002600102Q00070024001500122Q001500253Q00202Q00150015002600102Q00070027001500122Q001500283Q00202Q00150015002900122Q001600356Q001500020001000628000A00692Q013Q00046B3Q00692Q01000628000900692Q013Q00046B3Q00692Q01000628000700692Q013Q00046B3Q00692Q012Q00A7001300043Q001267001400366Q00130002000100102Q0007000E000900122Q001300253Q00202Q00130013002600102Q00070024001300122Q001300253Q00202Q00130013002600102Q00070027001300122Q001300283Q00202Q00130013002900122Q0014002A6Q0013000200010006280010007B2Q013Q00046B3Q007B2Q0100120A001300374Q00100013000100024Q0013000F6Q001300033Q00122Q001400013Q00122Q001500383Q00202Q00150015003900122Q0016003A6Q001700036Q00150017000200122Q001600036Q0013001600014Q001300043Q00122Q0014003B6Q00130002000100044Q00832Q012Q00A7001300033Q00122A001400013Q00122Q0015003C3Q00122Q0016000A6Q0013001600014Q001300043Q00122Q0014003D6Q0013000200012Q009C00136Q00AF00138Q001300106Q001400076Q00140001000200062Q0015008D2Q01001400046B3Q008D2Q0100202300150014000C0012780017000D4Q001900150017000200069E001600922Q01001400046B3Q00922Q0100202300160014000C001278001800304Q00190016001800020006280015001102013Q00046B3Q0011020100202300170014000C0012780019003E4Q0019001700190002000628001700CE2Q013Q00046B3Q00CE2Q0100120A0018003F3Q0020230019001700402Q008F0019001A4Q00AA00183Q001A00046B3Q00CC2Q01002023001D001C0041001278001F00424Q0019001D001F0002000628001D00B12Q013Q00046B3Q00B12Q012Q00A7001D00103Q002096001E001C00432Q0050001D00020002000628001D00B12Q013Q00046B3Q00B12Q012Q00A7001D00043Q001292001E00443Q00202Q001F001C00434Q001E001E001F4Q001D0002000100122Q001D002D3Q0006AE001E0001000100012Q00A83Q001C4Q0035001D00020001002023001D001C0041001278001F00454Q0019001D001F0002000628001D00CB2Q013Q00046B3Q00CB2Q01002096001D001C0043002080001D001D00464Q001D0002000200202Q001D001D004700122Q001F00486Q001D001F000200062Q001D00CB2Q013Q00046B3Q00CB2Q012Q00A7001D00043Q001222001E00493Q00202Q001F001C004300122Q0020004A3Q00122Q002100163Q00202Q0022001C004B4Q0021000200024Q001E001E00214Q001D0002000100122Q001D002D3Q0006AE001E0002000100012Q00A83Q001C4Q0035001D000200012Q0055001B5Q00065C0018009E2Q01000200046B3Q009E2Q0100309B0015004C002E00309B0015004D002E00209600180015000F002606001800D62Q01003300046B3Q00D62Q0100209600180015000F0006AB001800DC2Q01000B00046B3Q00DC2Q010010A40015000F000B2Q007E001800043Q00122Q0019004E6Q001A000B6Q00190019001A4Q001800020001002096001800150011002606001800E22Q01003300046B3Q00E22Q010020960018001500110006AB001800E82Q01000C00046B3Q00E82Q010010A400150011000C2Q007E001800043Q00122Q0019004F6Q001A000C6Q00190019001A4Q001800020001000628001600F12Q013Q00046B3Q00F12Q01002096001800160050000628001800F12Q013Q00046B3Q00F12Q0100309B00160050002E2Q00A7001800043Q001278001900514Q003500180002000100120A0018002D3Q0006AE00190003000100012Q00A83Q00154Q003500180002000100120A0018002D3Q0006AE00190004000100032Q00A73Q00114Q00A73Q00124Q00A73Q00044Q003500180002000100120A0018002D3Q0006AE00190005000100032Q00A73Q00134Q00A73Q00124Q00A73Q00044Q003500180002000100120A0018002D3Q0006AE00190006000100022Q00A73Q00134Q00A73Q00044Q003500180002000100120A001800283Q002096001800180052001278001900533Q0006AE001A0007000100062Q00A83Q00154Q00A83Q000B4Q00A83Q000C4Q00A83Q00164Q00A73Q00074Q00A73Q00104Q00730018001A00012Q004B001300024Q00663Q00013Q00083Q00043Q00030A3Q0052756E436F2Q6D616E64030C3Q00496E766F6B65536572766572030B3Q0053652Q6C436F6E6669726D03063Q004261736B6574000A4Q00147Q00206Q000100206Q000200122Q000200036Q00033Q00014Q000400013Q00102Q0003000400046Q00039Q008Q00017Q00013Q0003073Q0044657374726F7900044Q00A77Q0020235Q00012Q00353Q000200012Q00663Q00017Q00023Q0003053Q0056616C7565029Q00034Q00A77Q00309B3Q000100022Q00663Q00017Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q00047Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00023Q0003083Q004D6F76656D656E7403243Q005265736574206461736820632Q6F6C646F776E2076696120506C6179657253746174757300104Q00A78Q00973Q000100020006283Q000F00013Q00046B3Q000F000100209600013Q00010006280001000F00013Q00046B3Q000F00012Q00A7000100013Q00209600023Q00012Q00500001000200020006280001000F00013Q00046B3Q000F00012Q00A7000100023Q001278000200024Q00350001000200012Q00663Q00017Q000F3Q00030E3Q0046696E6446697273744368696C6403063Q0053686172656403083Q005061636B6167657303043Q004B6E697403073Q0072657175697265030D3Q00476574436F6E74726F2Q6C657203103Q00506C61796572436F6E74726F2Q6C657203063Q0053746174757303043Q004461746103083Q004D6F76656D656E7403383Q00526573657420506C61796572436F6E74726F2Q6C65722E5374617475732E446174612E4D6F76656D656E742E44617368432Q6F6C646F776E03133Q00436861726163746572436F6E74726F2Q6C657203093Q00432Q6F6C646F776E7303123Q005374616D696E61496E746572666163654364029Q003A4Q00337Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00046B3Q0009000100202300013Q0001001278000300034Q001900010003000200069E0002000E0001000100046B3Q000E0001002023000200010001001278000400044Q00190002000400020006280002003900013Q00046B3Q0039000100120A000300054Q00A8000400024Q00500003000200020020960004000300060006280004003900013Q00046B3Q00390001002096000400030006001278000500074Q00500004000200020006280004002F00013Q00046B3Q002F00010020960005000400080006280005002F00013Q00046B3Q002F00010020960005000400080020960006000500090006280006002F00013Q00046B3Q002F000100209600060005000900209600060006000A0006280006002F00013Q00046B3Q002F00012Q00A7000600013Q00209600070005000900209600070007000A2Q00500006000200020006280006002F00013Q00046B3Q002F00012Q00A7000600023Q0012780007000B4Q00350006000200010020960005000300060012780006000C4Q00500005000200020006280005003900013Q00046B3Q0039000100209600060005000D0006280006003900013Q00046B3Q0039000100209600060005000D00309B0006000E000F2Q00663Q00017Q000A3Q0003073Q007265717569726503063Q00536861726564030B3Q00496E707574416374696F6E03063Q00556E6C6F636B03043Q00456E756D03073Q004B6579436F646503013Q0051031E3Q00556E6C6F636B65642051206B65792076696120496E707574416374696F6E03093Q00556E6C6F636B412Q6C03053Q00436C656172001D3Q0012703Q00016Q00015Q00202Q00010001000200202Q0001000100036Q0002000200064Q001C00013Q00046B3Q001C000100209600013Q00040006280001001200013Q00046B3Q0012000100202300013Q0004001260000300053Q00202Q00030003000600202Q0003000300074Q0001000300014Q000100013Q00122Q000200086Q00010002000100209600013Q00090006280001001700013Q00046B3Q0017000100202300013Q00092Q003500010002000100209600013Q000A0006280001001C00013Q00046B3Q001C000100202300013Q000A2Q00350001000200012Q00663Q00017Q000F3Q00030D3Q00506C6174666F726D5374616E6401002Q033Q0053697403093Q0057616C6B53702Q6564028Q0003093Q004A756D70506F77657203053Q007063612Q6C03083Q00416E63686F726564030E3Q0046696E6446697273744368696C6403063Q0053746174757303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q00422Q6F6C56616C756503043Q004E616D6500424Q00A77Q0006283Q001900013Q00046B3Q001900012Q00A77Q0030493Q000100029Q0000304Q000300029Q0000206Q000400264Q000E0001000500046B3Q000E00012Q00A78Q00A7000100013Q0010A43Q000400012Q00A77Q0020965Q000600264E3Q00150001000500046B3Q001500012Q00A78Q00A7000100023Q0010A43Q0006000100120A3Q00073Q0006AE00013Q000100012Q00A78Q00353Q000200012Q00A73Q00033Q0006283Q002200013Q00046B3Q002200012Q00A73Q00033Q0020965Q00080006283Q002200013Q00046B3Q002200012Q00A73Q00033Q00309B3Q000800022Q00A73Q00044Q00973Q0001000200069E0001002900013Q00046B3Q0029000100202300013Q00090012780003000A4Q00190001000300020006280001004100013Q00046B3Q0041000100120A0002000B3Q00202300030001000C2Q008F000300044Q00AA00023Q000400046B3Q003F000100202300070006000D0012780009000E4Q00190007000900020006280007003E00013Q00046B3Q003E00012Q00A7000700053Q00209600080006000F2Q00500007000200020006280007003E00013Q00046B3Q003E000100120A000700073Q0006AE00080001000100012Q00A83Q00064Q00350007000200012Q005500055Q00065C000200300001000200046B3Q003000012Q00663Q00013Q00023Q00043Q00030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q0052752Q6E696E6700074Q00047Q00206Q000100122Q000200023Q00202Q00020002000300202Q0002000200046Q000200016Q00017Q00013Q0003073Q0044657374726F7900044Q00A77Q0020235Q00012Q00353Q000200012Q00663Q00017Q00023Q0003043Q007461736B03053Q00737061776E00104Q00A77Q0006283Q000400013Q00046B3Q000400012Q00663Q00013Q00120A3Q00013Q0020965Q00020006AE00013Q000100062Q00A73Q00014Q00A73Q00024Q00A73Q00034Q00A73Q00044Q00A73Q00054Q00A78Q00503Q000200022Q00018Q00663Q00013Q00013Q000C3Q0003083Q004175746F53652Q6C03043Q007461736B03043Q0077616974026Q00E03F03043Q007469636B030C3Q0053652Q6C496E74657276616C03203Q004175746F2053652Q6C3A20547279696E67206E6F2D74656C65706F72743Q2E030A3Q006E6F54656C65706F72742Q01026Q00F03F033C3Q004175746F2053652Q6C3A204E6F2D74656C65706F7274206661696C65642C2066612Q6C6261636B20746F20666F7263652074656C65706F72743Q2E030D3Q00666F72636554656C65706F727400374Q00A77Q0020965Q00010006283Q003400013Q00046B3Q0034000100120A3Q00023Q0020815Q000300122Q000100048Q000200019Q0000206Q000100064Q000D0001000100046B3Q000D000100046B3Q003400012Q00A73Q00013Q00060F5Q0001000100046B5Q000100120A3Q00054Q00513Q000100024Q000100029Q0000014Q00015Q00202Q00010001000600062Q00013Q00013Q00046B5Q00012Q00A73Q00033Q001279000100078Q000200016Q00046Q00013Q000100302Q0001000800096Q0002000200066Q0001000100046B5Q00012Q00A700015Q00209600010001000100062800013Q00013Q00046B5Q000100120A000100023Q00208900010001000300122Q0002000A6Q0001000200014Q000100013Q00062Q00013Q0001000100046B5Q00012Q00A7000100033Q00122Q0002000B6Q0001000200014Q000100046Q00023Q000100302Q0002000C00094Q00010002000100046Q00012Q00098Q00013Q00054Q00663Q00017Q00023Q0003083Q004175746F53652Q6C012Q00034Q00A77Q00309B3Q000100022Q00663Q00017Q000C3Q0003083Q004175746F53652Q6C0100028Q0003053Q00706169727303023Q005F4703053Q00466F72676503103Q00506C617965725549456C656D656E7473030E3Q004175746F53652Q6C546F2Q676C6503053Q007063612Q6C03123Q0053652Q6C496E74657276616C536C6964657203133Q00536B69704661766F7269746573546F2Q676C6503183Q00436F6E66696720726573657420746F2064656661756C747300304Q00407Q00304Q000100029Q006Q00019Q008Q00023Q00124Q00038Q00033Q00124Q00046Q000100048Q0002000200044Q000E00012Q00A700056Q003900050003000400065C3Q000C0001000200046B3Q000C000100120A3Q00053Q0020965Q00060020965Q00070006283Q002C00013Q00046B3Q002C000100209600013Q00080006280001001C00013Q00046B3Q001C000100120A000100093Q0006AE00023Q000100012Q00A88Q003500010002000100209600013Q000A0006280001002400013Q00046B3Q0024000100120A000100093Q0006AE00020001000100022Q00A88Q00A73Q00044Q003500010002000100209600013Q000B0006280001002C00013Q00046B3Q002C000100120A000100093Q0006AE00020002000100022Q00A88Q00A73Q00044Q00350001000200012Q00A7000100053Q0012780002000C4Q00350001000200012Q00663Q00013Q00033Q00023Q00030E3Q004175746F53652Q6C546F2Q676C652Q033Q0053657400064Q00217Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003123Q0053652Q6C496E74657276616C536C696465722Q033Q00536574030C3Q0053652Q6C496E74657276616C00074Q00157Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003133Q00536B69704661766F7269746573546F2Q676C652Q033Q00536574030D3Q00536B69704661766F726974657300074Q00157Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00023Q00030A3Q006E6F54656C65706F72742Q0100064Q00829Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00023Q00030D3Q00666F72636554656C65706F72742Q0100064Q00829Q0000013Q000100302Q0001000100026Q00019Q008Q00017Q00013Q0003103Q00436C65616E757020636F6D706C65746500084Q00859Q003Q000100016Q00018Q000100016Q00023Q00122Q000100018Q000200016Q00017Q00", GetFEnv(), ...);
